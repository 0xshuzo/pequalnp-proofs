import PEqualNP.Defs

-- The Live/Run/Forest checker derives from PressF10, pequalnp-proofs PR 4332,
-- and its extension in L_meta_3853, licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_10494
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 512
def zero : Sig := 0
def one : Sig := BitVec.allOnes 512
def neg (a : Sig) : Sig := ~~~a
def bin (d : Bool) (a b : Sig) : Sig := if d then a ||| b else a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
private theorem bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d <;> simp [bin,BitVec.and_comm,BitVec.or_comm]

inductive Live (target : Sig) : Nat → Nat → Finset Sig → Prop
  | stop (hp : proper target) : Live target 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live target k t (insert (neg a) U)) :
      Live target (k+1) (t+1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live target k t (insert (bin d a b) U)) :
      Live target (k+1) t (insert a (insert b U))

private lemma live_proper {k t S} (h : Live target k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop hp => simpa using hp
  | unary ha hf _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {k t S} (h : Live target k t S) : t ≤ k ∧ S.card+t ≤ k+1 := by
  induction h with
  | stop hp => simp
  | @unary k t U a ha hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega,by omega⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega,by omega⟩


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v

private lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)

private lemma bin_laws (a : Sig) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  simp only [bin,one,zero,Bool.false_eq_true,ite_false,ite_true,BitVec.and_allOnes,BitVec.or_zero,BitVec.and_zero,BitVec.or_allOnes,BitVec.and_self,BitVec.or_self,and_self] <;> simp

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)

private lemma bin_rep {w a b} (d : Bool) (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a0,az,ao,aa,aa'⟩ := bin_laws a
  obtain ⟨b1,b0,bz,bo,bb,bb'⟩ := bin_laws b
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a=b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d,a,b,ham,hbm,hap,hbp,he,rfl⟩)

private lemma gate_rep (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  have nx (a : Sig) (ha : represented w a) : represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (get_rep w i)
    | cons j l =>
      cases l with
      | cons a l => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).1] using bin_rep false (get_rep w i) (get_rep w j)
        · simpa only [gv,List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,(bin_laws _).2.1] using bin_rep true (get_rep w i) (get_rep w j)
        · exact nx _ (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live target k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live target k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,t,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a,ha,hp',eq⟩ | ⟨d,a,b,ha,hb,pa,pb,hab,eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live target k t (insert (neg a) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_,_,_,Nat.le_refl _,Live.unary hp' hf ht,by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live target k t (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
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
        exact ⟨_,_,_,Nat.le_refl _,Live.binary pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,t,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (hp : proper target) (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live target k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0,0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,t,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l,u,T,hl,hu,hT⟩ := pull_gate ht (gate_rep w g (legal g (by simp))) hs
    exact ⟨l,u,T,by simp; omega,hu,hT⟩

def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [bit,bin]

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
      change bit i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
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

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (pool : List (Wire R)) (v : Wire R) : Prop := v ∈ pool ∨ Constant v

def supply {R} (pool xs : List (Wire R)) := ∀ a ∈ xs, Available pool a

inductive Reach {R} (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | start : Reach roots 0 roots
  | one {p bank a} : Reach roots p bank → Available bank a →
      Reach roots (p+1) (inv a :: bank)
  | two {p bank a b} (op : Bool) : Reach roots p bank → Available bank a →
      Available bank b → Reach roots (p+1) (combine op a b :: bank)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

inductive Run {R} (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : Run goal 0 [goal]
  | perm {s xs zs} : xs.Perm zs → Run goal s xs → Run goal s zs
  | one {s a rest} (save : Bool) : Run goal s (inv a :: kept save a rest) →
      Run goal (s+1) (a::rest)
  | two {s a b rest} (op ka kb : Bool) :
      Run goal s (combine op a b :: kept ka a (kept kb b rest)) →
      Run goal (s+1) (a::b::rest)

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available bank a) (hb : Available bank b) :
    Available bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩
  · cases op <;> cases v
    · exact Or.inr ⟨false, by funext x; simp [combine]⟩
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr ⟨true, by funext x; simp [combine]⟩

theorem available_cons {R} {bank v} (w : Wire R) (h : Available bank v) :
    Available (w::bank) v := by
  exact h.elim (fun h => Or.inl (List.mem_cons_of_mem _ h)) Or.inr

theorem extend_one {R} (roots : List (Wire R)) {p bank a} (hp : Reach roots p bank)
    (ha : Available bank a) :
    ∃ q next, Reach roots q next ∧ Available next (inv a) ∧
        (∀ v, Available bank v → Available next v) ∧ q+cost a ≤ p+1+cost (inv a) := by
  classical
  by_cases c : Constant a
  · exact ⟨p,bank,hp,Or.inr (inv_constant c),fun _ h => h,by simp [cost,c,inv_constant c]⟩
  · exact ⟨p+1,_,Reach.one hp ha,Or.inl (by simp),fun _ h => available_cons _ h,by simp [cost,c]⟩

theorem extend_two {R} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach roots p bank)
    (ha : Available bank a) (hb : Available bank b) :
    ∃ q next, Reach roots q next ∧ Available next (combine op a b) ∧
        (∀ v, Available bank v → Available next v) ∧
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

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach roots p bank) (hs : supply bank ws) :
    ∃ q next, Reach roots q next ∧ Available next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @one s a rest save _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_one roots hp (hs a (by simp))
    have ht : supply T (inv a :: kept save a rest) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · exact inc v (hs v (List.mem_cons.mpr (mem_kept hh)))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a rest save
    rw [mass_cons] at hl ⊢
    exact ⟨q,W,hW,hv,by omega⟩
  | @two s a b rest op ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_two roots op hp (hs a (by simp)) (hs b (by simp))
    have ht : supply T (combine op a b :: kept ka a (kept kb b rest)) := by
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

theorem restrict_run {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws) :
    Run (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | one save _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    exact Run.one save ih
  | two op ka kb _ ih =>
    simp only [List.map_cons,restrict_kept] at ih ⊢
    cases op
    · exact Run.two false ka kb ih
    · exact Run.two true ka kb ih

theorem projected_bound {R S : Type} (rows : S → R) {goal s ws} (h : Run goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach roots p bank) (hs : supply bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach roots q bs → Available bs (restrictRows rows goal) → L ≤ q) :
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

theorem obs_bin (d : Bool) (a b : Sig) :
    observe (bin d a b) = combine d (observe a) (observe b) := by
  funext r
  cases d <;> exact bit_bin _ _ _ _

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {T : Sig} {k u S} (h : Live T k u S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run (observe T) k (v.map observe) := by
  classical
  induction h generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @unary k u U a ha fresh _ ih =>
    let rest := (U.erase a).toList
    let save := decide (a ∈ U)
    let tail := kept save a rest
    have er : rest.toFinset = U.erase a := by simp [rest]
    have hm : a ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have ht : tail.toFinset = U := by
      rw [show tail=kept save a rest by rfl,kept_fin,er]
      by_cases hh : a ∈ U <;> simp [save,hh]
    have nd := kept_nd save a rest hr hm
    have hf : neg a ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz))
    have progress := ih (neg a::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    rw [List.map_cons,map_kept,obs_neg] at progress
    have perm : (a::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (List.nodup_cons.mpr ⟨hm,hr⟩) hv
      simp [er,eqv]
    exact Run.perm (perm.map _) (Run.one save progress)
  | @binary k u U a b d ha hb hab fresh _ ih =>
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
    change Run _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_bin (d : Bool) (f g : Wire Row) :
    table (combine d f g) = bin d (table f) (table g) := by
  rw [←table_observe (bin d (table f) (table g)),obs_bin,observe_table,observe_table]

theorem available_rep {bank : List (Wire Row)} {a} (h : Available bank a) :
    represented (bank.map table) (table a) := by
  rcases h with hm | ⟨b,rfl⟩
  · exact Or.inl (List.mem_map_of_mem hm)
  · apply Or.inr
    cases b
    · have z : table (fun _ => false) = zero := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_zero ⟨j,hj⟩).symm
      exact fun hp => hp.1 z
    · have z : table (fun _ => true) = one := by
        apply BitVec.eq_of_getLsbD_eq
        intro j hj
        exact (bit_table _ ⟨j,hj⟩).trans (bit_one ⟨j,hj⟩).symm
      exact fun hp => hp.2 z

theorem inv_rep {w a} (ha : represented w a) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases ha with rfl | rfl | ⟨hm,hp⟩
  · exact Or.inl (Or.inr fun h => h.2 neg_laws.1)
  · exact Or.inl (Or.inr fun h => h.1 neg_laws.2)
  · exact Or.inr (Or.inl ⟨a,hm,hp,rfl⟩)

theorem pull_cons {w : List Sig} {z : Sig} {T k t S} (h : Live T k t S)
    (hz : represented w z ∨ witness w z) (hs : ∀ a ∈ S, a ∈ z::w) :
    ∃ k' t' S', k' ≤ k+1 ∧ Live T k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  apply pull_gate h hz
  intro a hm
  simpa [or_comm] using hs a hm

theorem reach_live_sub {roots : List (Wire Row)} {p bank}
    (h : Reach roots p bank) {T k t S} (run : Live T k t S)
    (sub : ∀ a ∈ S, a ∈ bank.map table) :
    ∃ l v U, l ≤ p+k ∧ Live T l v U ∧ ∀ a ∈ U, a ∈ roots.map table := by
  induction h generalizing k t S with
  | start => exact ⟨k,t,S,by omega,run,sub⟩
  | @one p bank a h ha ih =>
    rw [List.map_cons,table_inv] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (inv_rep (available_rep ha)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,table_bin] at sub
    obtain ⟨k',t',S',hk,run',sub'⟩ := pull_cons run (bin_rep d (available_rep ha) (available_rep hb)) sub
    obtain ⟨l,v,U,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,v,U,by omega,hr,hs⟩

theorem reach_live {roots : List Sig} {p bank T} (hp : proper T)
    (h : Reach (roots.map observe) p bank) (hit : Available bank (observe T)) :
    ∃ k t S, k ≤ p ∧ Live T k t S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,v,U,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,v,U,by omega,hr,?_⟩
  simpa [List.map_map,Function.comp_def,table_observe] using hs

theorem live_row_difference {T k t S} (h : Live T k t S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @unary k t U a hp hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · refine ⟨a,by simp,?_⟩
      exact fun he => hd (by rw [bit_neg,bit_neg,he])
    · exact ⟨v,Finset.mem_insert_of_mem hu,hd⟩
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {T k t S} (h : Live T k t S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_neg (f : Row → Row) (a : Sig) : rename f (neg a) = neg (rename f a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (neg a)) = bit ⟨j,hj⟩ (neg (rename f a))
  rw [bit_rename,bit_neg,bit_neg,bit_rename]
theorem rename_bin (f : Row → Row) (d : Bool) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  change bit ⟨j,hj⟩ (rename f (bin d a b)) = bit ⟨j,hj⟩ (bin d (rename f a) (rename f b))
  rw [bit_rename,bit_bin,bit_bin,bit_rename,bit_rename]
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
theorem live_rename {T k t S} (h : Live T k t S) (f : Row → Row) (onto : Function.Surjective f) :
    Live (rename f T) k t (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @unary k t U a hp hf _ ih =>
    have fresh : rename f (neg a) ∉ (insert a U).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_neg] at fresh ih ⊢
    exact Live.unary (pp _ hp) fresh ih
  | @binary k t U a b d ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {T k t S} (h : Live T k t S) (none : t=0) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | unary _ _ _ _ => omega
  | @binary k t U a b d ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih none
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      cases d <;> cases p : bit r a <;> cases q : bit s a <;>
        cases u : bit r b <;> cases z : bit s b <;> simp_all
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map observe) p bank → Available bank (observe T) → L ≤ p

def Impossible (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k t, k ≤ cap → ¬Live T k t S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {roots T L} (hp : proper T)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,t,S,hk,run,hs⟩ := reach_live hp h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k t (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : represented ([] : List Sig) v := by
    have avail : Available ([] : List (Wire Row)) (observe v) := Or.inr ⟨b,h⟩
    simpa only [List.map_nil,table_observe] using available_rep avail
  exact (hr.resolve_left (by simp)) hv

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

theorem lower_slice {roots other : List Sig} {T G : Sig} (pT : proper T) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live pT hh ha
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
  have supp : supply (other.map observe) ((front.map observe).map (restrictRows r)) := by
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



def childOne (ws : List Sig) (a : Sig) (keep : Bool) : List Sig :=
  neg a :: kept keep a (ws.erase a)
def childTwo (ws : List Sig) (a b : Sig) (d ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (oneStep : ∀ a ∈ ws, ∀ keep, neg a ∉ ws → proper (neg a) →
      (childOne ws a keep).length ≤ cap →
      Impossible T (cap-1) (childOne ws a keep).toFinset)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k t hk h
  generalize he : ws.toFinset = S at h
  cases h with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @unary k t U a ha hf tail =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have fresh : neg a ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let keep := decide (a ∈ U)
    have er := erase_fin hn a
    have rest : (kept keep a (ws.erase a)).toFinset = U := by
      rw [kept_fin,er,he]
      by_cases hm : a ∈ U <;> simp [keep,hm]
    have nd : (childOne ws a keep).Nodup := by
      have na : a ∉ ws.erase a := hn.not_mem_erase
      have nk := kept_nd keep a (ws.erase a) (hn.erase _) na
      refine List.nodup_cons.mpr ⟨?_,nk⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (rest ▸ List.mem_toFinset.mpr h))
    have eq : (childOne ws a keep).toFinset = insert (neg a) U := by simp [childOne,rest]
    have sc := (live_size tail).2
    have len : (childOne ws a keep).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact oneStep a am keep fresh hz len k t (by omega) (eq.symm ▸ tail)
  | @binary k t U a b d ha hb hab hf tail =>
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
    have sc := (live_size tail).2
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d ka kb hab fresh hz len k t (by omega) (eq.symm ▸ tail)

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

theorem cover_sound {T k t S} (h : Live T k t S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → t=0) :
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

theorem cover_required {T cap ws k t} (h : Live T k t (List.toFinset ws))
    (hk : k ≤ cap) (hn : ws.Nodup) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (decide (ws.length=cap+1)) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  intro hh
  have eq := of_decide_eq_true hh
  have bound := (live_size h).2
  rw [List.toFinset_card_of_nodup hn] at bound
  omega



def Slice (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach (roots.map observe) p bank → Available bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m)

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

def poolSupply (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available bank (restrictRows f (observe a))

theorem availableB_sound {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply f bank pool)
    (check : availableB d pool a = true) : Available bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with (hz | ho) | ⟨v,hv,he⟩
  · exact Or.inr ⟨false,masked_zero dom hz⟩
  · exact Or.inr ⟨true,masked_one dom ho⟩
  · exact masked_eq dom he ▸ supplyB v hv

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) :=
  if c.1=2 then neg c.2.1 else bin (c.1==1) c.2.1 c.2.2
def choiceOK (d : Sig) (pool : List Sig) (c : Choice) :=
  availableB d pool c.2.1 && (c.1==2 || availableB d pool c.2.2)

theorem pay_choice {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d pool c = true) :
    ∃ next, Reach roots (q+1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  have ok : availableB d pool c.2.1 = true ∧ (c.1==2 || availableB d pool c.2.2) = true := by simpa only [choiceOK,Bool.and_eq_true] using valid
  have ha := availableB_sound dom hs ok.1
  let z := restrictRows f (observe (choiceVal c))
  have hz : Reach roots (q+1) (z::bank) := by
    by_cases unary : c.1=2
    · change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_pos unary,obs_neg]
      exact Reach.one hp ha
    · have hb : availableB d pool c.2.2 = true := by simpa [unary] using ok.2
      have hz' := Reach.two (c.1==1) hp ha (availableB_sound dom hs hb)
      change Reach _ _ (restrictRows f (observe (choiceVal c)) :: _)
      rw [choiceVal,if_neg unary,obs_bin]
      have comm (b : Bool) (v w : Wire Row) : restrictRows f (combine b v w) = combine b (restrictRows f v) (restrictRows f w) := by cases b <;> rfl
      rw [comm]
      exact hz'
  refine ⟨_,hz,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Or.inl (by simp [z])
  · exact available_cons _ (hs _ hm)

def makePool (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK d pool c then makePool d (choiceVal c::pool) cs else none

theorem makePool_sound {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {result} (ok : makePool d pool cs = some result) :
    ∃ next, Reach roots (q+cs.length) next ∧ poolSupply f next result := by
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

def poolCut (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB d pool)

theorem poolCut_sound {raw T d L} (slice : Slice raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut d L cap cs.length pool ws = true) :
    Impossible T cap ws.toFinset := by
  intro k t hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply bank ((ws.map observe).map (restrictRows f)) := by
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
theorem freeWord_ok {roots w} (ok : freeWord roots w = true) :
    Available (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr ⟨false,funext bit_zero⟩
  · exact Or.inr ⟨true,funext bit_one⟩
  · exact Or.inl (List.mem_map_of_mem hm)

def checkMap (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  movedWord ms T == G && raw.all (fun a => freeWord base (movedWord ms a))

theorem map_correct {ms raw T base G} (ok : checkMap ms raw T base G = true) :
    rename (movedRow ms) T = G ∧
    ∀ a ∈ raw, Available (base.map observe) (observe (rename (movedRow ms) a)) := by
  simp only [checkMap,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,moved_eq_rename] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩

theorem lower_map {ms raw T base G L} (ok : checkMap ms raw T base G = true)
    (pT : proper T) (pG : proper G) (hL : Lower base G L) : Lower raw T L := by
  obtain ⟨eq,supp⟩ := map_correct ok
  simpa using lower_slice pT pG (movedRow ms) eq supp ∅ (by simp) (by simp) L hL

theorem slice_correct {ms raw T base G L d} (ok : checkMap ms raw T base G = true)
    (all : movedWord ms d = one) (properG : proper G) (hL : Lower base G L) :
    Slice raw T d L := by
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
  xs.all (fun a => witnessB T raw a.1 a.2)
theorem essential_ok {T raw xs} (ok : checkEssential T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, Essential T raw a := by
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact witnessB_sound (List.all_eq_true.mp ok _ hm)

theorem lower_count {raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : checkEssential T raw xs = true) :
    Lower raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,t,S,hk,run,sub⟩ := reach_live properT hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := essential_ok ok a ha
    exact raw_required run raw a sub r s hd iso
  have bound := (live_size run).2
  omega

def checkLift (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  checkMap ms raw T base G && checkEssential T raw xs &&
    xs.all (fun a => movedWord ms a.1 == zero || movedWord ms a.1 == one)

theorem lift_ok {ms T raw base G xs L} (ok : checkLift ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower base G L) :
    Lower raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [checkLift,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := map_correct ok.1.1
  apply lower_slice properT properG _ eq supp _ (essential_ok ok.1.2) _ L low
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
def vertex (m j : Nat) := if m.testBit j then (if m.testBit 9 && j == 4 then neg (inputs.getD 4 zero) else inputs.getD j zero) else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 0 &&& x 8) ||| (x 2 &&& x 8) ||| (x 6 &&& x 8) ||| (x 7 &&& x 8)
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

def supportPairs (baseRow mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) => (a,Fin.ofNat 512 baseRow,Fin.ofNat 512 (baseRow ^^^ (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  let base := if m.testBit 9 && m.testBit 4 then 16 else 0
  (selected m).map fun (i,a) =>
    let r := base ^^^ (1 <<< ((hints >>> (4*i)) &&& 15))
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ^^^ (1 <<< i)))

def properB (T : Sig) := T != zero && T != one
theorem proper_of (T : Sig) (h : properB T = true) : proper T := by
  simpa only [properB,proper,Bool.and_eq_true,bne_iff_ne] using h
def assertSize (m hints L : Nat) :=
  let xs := graphPairs m hints
  properB (graphGoal m) && checkEssential (graphGoal m) (vars m) xs &&
    decide (L ≤ (xs.map Prod.fst).toFinset.card-1)
theorem size_of {m hints L} (h : assertSize m hints L = true) :
    Lower (vars m) (graphGoal m) L := by
  simp only [assertSize,Bool.and_eq_true,decide_eq_true_eq] at h
  intro p bank hr ha
  exact h.2.trans (lower_count (proper_of _ h.1.1) _ h.1.2 p bank hr ha)

abbrev ColumnInfo := Nat × Nat × Nat × Nat × Nat
def colFree (m z o : Nat) := (m &&& 511) ^^^ ((m &&& 511) &&& (z ||| o))
def chartGoal (m : Nat) : Sig := graphGoal m
def colCheck (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  let count := (xs.map Prod.fst).toFinset.card
  let drop := colFree free q 0
  let lz := if m.testBit 9 && drop.testBit 4 then drop &&& (511 ^^^ 16) else drop
  let lo := if m.testBit 9 && drop.testBit 4 then 16 else 0
  properB G && checkMap ms (vars m) (chartGoal m) (vars free) G &&
    (movedWord ms (subcube z o)==one) &&
    (if q=0 then checkEssential G (vars free) xs && decide (L ≤ count-1)
     else properB (graphGoal q) &&
       checkLift (fixRows lz lo) G (vars free) (vars q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))

theorem col_sound {m : Nat} (c : ColumnInfo) (prior : Nat → Nat)
    (valid : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck m c prior = true) : Slice (vars m) (chartGoal m) (subcube c.1 c.2.1) c.2.2.2.2 := by
  obtain ⟨z,o,q,s,L⟩ := c
  let ms := fixRows z o
  let free := colFree m z o
  let G := movedWord ms (chartGoal m)
  let baseRow := if m.testBit 9 && free.testBit 4 then 16 else 0
  let xs := supportPairs baseRow s
  change (((properB G && checkMap ms (vars m) (chartGoal m) (vars free) G) &&
    (movedWord ms (subcube z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply slice_correct ok.1.1.2 ok.1.2 (proper_of _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [colCheck,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lower_count (proper_of _ ok.1.1.1) _ hh.1 p bank hr ha)
  · simp only [colCheck,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (proper_of _ ok.1.1.1) (proper_of _ hh.1.1) (valid q) p bank hr ha)

def relabelOK (old rep : Nat) (swaps : List Nat) :=
  properB (graphGoal old) && properB (graphGoal rep) &&
    checkMap (swaps.map swapRows) (vars old) (graphGoal old) (vars rep) (graphGoal rep)
theorem relabel_of {old rep L swaps} (ok : relabelOK old rep swaps = true)
    (h : Lower (vars rep) (graphGoal rep) L) : Lower (vars old) (graphGoal old) L := by
  simp only [relabelOK,Bool.and_eq_true] at ok
  exact lower_map ok.2 (proper_of _ ok.1.1) (proper_of _ ok.1.2) h

def boundsBefore (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0
theorem before_sound (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower (vars q) (graphGoal q) (boundsBefore entries q) := by
  unfold boundsBefore
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


structure BoundPool where
  domain : Sig
  bound : Nat
  paid : Nat
  wires : List Sig

def ValidPool (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬Constant (restrictRows f (observe T)) ∧
    (∀ q ws, Reach (roots.map observe) q ws → Available ws (restrictRows f (observe T)) → c.bound ≤ q) ∧
    Reach (roots.map observe) c.paid bank ∧ poolSupply f bank c.wires ∧ True

theorem build_valid {raw T d lb} (h : Slice raw T d lb) (cs : List Choice) {ws}
    (build : makePool d raw cs = some ws) : ValidPool raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa using hr,hs,trivial⟩

theorem valid_exclude {raw T c} (valid : ValidPool raw T c) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (known : ∀ a ∈ rest, availableB c.domain c.wires a = true)
    (buy : if paid then choiceOK c.domain c.wires choice = true
       else availableB c.domain c.wires (choiceVal choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (isMaskedConstant c.domain))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible T k (choiceVal choice :: rest).toFinset := by
  intro t num ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := choiceVal choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach (roots.map observe) n out)
      (zs : poolSupply f out (choiceVal choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : supply out ((ws.map observe).map (restrictRows f)) := by
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
    · have avail := availableB_sound dom hs (known _ hm)
      rcases avail with mem | con
      · have ha : availableB c.domain c.wires a = true := known _ hm
        have point : ∀ u ∈ c.wires, Available out (restrictRows f (observe u)) :=
          fun u hu => hc u (List.mem_cons_of_mem _ hu)
        exact availableB_sound dom point ha
      · exact Or.inr con

def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Sig) (op : Choice) :=
  let z := choiceVal op
  let extra := !(availableB c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (isMaskedConstant c.domain)) &&
    rest.all (availableB c.domain c.wires)) && (!extra || choiceOK c.domain c.wires op)

theorem scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op::rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op::rest).toFinset := by
  let extra := !(availableB c.domain c.wires (choiceVal op))
  apply valid_exclude valid k rest op extra _ _ _ nd
  · simp only [scalarPoolCut,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [scalarPoolCut,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : availableB c.domain c.wires (choiceVal op) <;> simp_all [extra]
  · simp only [scalarPoolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1

def materialize (raw : List Sig) (cs : List Choice) (d : Sig) (lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)
theorem materialize_sound {raw T d L cs c} (slice : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact build_valid slice cs he


abbrev Bits := BitVec 512
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 512 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 512 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 512 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 512 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 512 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 512 → Row) (d : Bool) (a b : Sig) :
    ofRows r (bin d a b) = if d then ofRows r a ||| ofRows r b else ofRows r a &&& ofRows r b := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (bin d a b) ⟨j,hj⟩
  rw [bit_bin,←ofRows_bit r a ⟨j,hj⟩,←ofRows_bit r b ⟨j,hj⟩] at h
  cases d <;> simpa only [Bool.false_eq_true,ite_false,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_or] using h
theorem faithful_neg {r s x} (h : faithful r s x) : faithful r s (dneg x) := by
  change x.2 = _ at h
  simp only [faithful,dneg,pairSig,ofRows_neg, h]
theorem faithful_bin {r s x y} (d) (hx : faithful r s x) (hy : faithful r s y) :
    faithful r s (dbin d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  cases d <;> simp only [faithful,dbin,Bool.false_eq_true,ite_false,ite_true,pairSig,ofRows_bin,hx,hy]

def codeDecor (op : Nat) (x y : Decor) := if op=2 then dneg x else dbin (op==1) x y
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
    decodeBank k (bits >>> 10) (ws++[codeDecor ((bits >>> 8) &&& 3) a b])
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
      unfold codeDecor
      split
      · exact faithful_neg (faithful_get base _)
      · exact faithful_bin _ (faithful_get base _) (faithful_get base _)

def asRow (cols : Nat → Bits) (i : Fin 512) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 512) (j : Fin 9) :
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
  let x := fun j => if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 0 &&& x 8) ||| (x 2 &&& x 8) ||| (x 6 &&& x 8) ||| (x 7 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 512) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then (if m.testBit 9 && j.val == 4 then ~~~(v 4) else v j.val) else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · by_cases hf : (m.testBit 9 && j.val == 4) = true
    · have hj4 : j.val = 4 := by
        simp only [Bool.and_eq_true, beq_iff_eq] at hf; exact hf.2
      simp only [vertex, hh, hf, ite_true, bit_neg, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
      exact congrArg Bool.not (asRow_bit v i ⟨4, by decide⟩)
    · simpa [vertex, hh, hf] using asRow_bit v i j
  · simp [vertex, hh, bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 512) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
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

def closeChild (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : Choice) :=
  let ws := choiceVal op::rest
  (links (keySet ws)).any (sameWords ws) || pools.any (fun p => scalarPoolCut p k rest op)

theorem closeChild_sound {raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, ValidPool raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → Impossible T k (List.toFinset xs))
    (nd : (choiceVal op :: rest).Nodup)
    (h : closeChild pools links k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChild,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [sameWords_sound ok]
    exact lValid _ _ hx
  · exact scalarPoolCut_sound (pValid _ hp) nd ok

abbrev CovPair := Cov × Cov
def preCov (ws : List Decor) : CovPair := (coverage false ws,coverage true ws)
def getCov (c : CovPair) (d : Bool) := if d then c.2 else c.1
theorem get_preCov (ws) (d : Bool) : getCov (preCov ws) d = coverage d ws := by cases d <;> rfl
def restCov (v : Cov) (a b : Bits) (un ka kb : Bool) :=
  if un then (if ka then v.1 else takeOne v a) else
    if ka then (if kb then v.1 else takeOne v b)
    else if kb then takeOne v a else takeTwo v a b
def opKeep (un ka kb : Bool) (a b : Decor) (ws : List Decor) :=
  if un then delOne ws a ka else delTwo ws a b ka kb

theorem rest_coverage {ws : List Decor} {a b : Decor} (ha : a ∈ ws) (hb : b ∈ ws)
    (un ka kb d : Bool) (ne : un=false → a≠b) :
    (coverage d (opKeep un ka kb a b ws)).1 =
      restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) un ka kb := by
  rw [get_preCov]
  cases un
  · exact cover_two d a b ha hb (ne rfl) ka kb
  · exact cover_one d a ha ka

theorem delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _
theorem keep_sub (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    (opKeep un ka kb a b ws).Sublist ws := by
  cases un
  · exact (delOne_sub _ _ _).trans (delOne_sub _ _ _)
  · exact delOne_sub _ _ _
theorem len_keep (ws : List Decor) (a b : Decor) (un ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : un=false → a≠b) :
    (opKeep un ka kb a b ws).length =
      ws.length - (if ka then 0 else 1) - (if un || kb then 0 else 1) := by
  cases un
  · have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm (ne rfl))).mpr hb
    cases ka <;> cases kb <;> simp [opKeep,delTwo,delOne,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]
  · cases ka <;> cases kb <;> simp [opKeep,delOne,List.length_erase_of_mem ha]

def movedDecor (op : Nat) (a b : Decor) := codeDecor op a b
def movedChoice (op : Nat) (a b : Decor) : Choice := (op,a.1,b.1)
theorem moved_full (op) (a b : Decor) :
    (movedDecor op a b).1 = choiceVal (movedChoice op a b) := by
  by_cases h : op=2
  · simp [movedDecor,codeDecor,h,dneg,choiceVal,movedChoice]
  · cases hh : op==1 <;> simp [movedDecor,codeDecor,h,hh,dbin,choiceVal,movedChoice]
theorem moved_faithful {r s a b} (ha : faithful r s a) (hb : faithful r s b) (op : Nat) :
    faithful r s (movedDecor op a b) := by
  unfold movedDecor codeDecor
  split
  · exact faithful_neg ha
  · exact faithful_bin _ ha hb

abbrev NodeContext := Nat × Nat × List Decor × CovPair × List BoundPool × (Nat → List (List Sig))
def evalMove (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let un := op==2
  let len := 1+(n - (if ka then 0 else 1) - (if un || kb then 0 else 1))
  if len>cap then true else
    let d := len==cap
    let rs := restCov (getCov cov d) (column d a.2) (column d b.2) un ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 512 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (opKeep un ka kb a b ws).map Prod.fst
      closeChild pools links (cap-1) rest (movedChoice op a b)

def moveFront (ws : List Decor) (op : Nat) (a b : Decor) (ka kb : Bool) :=
  (movedDecor op a b).1 :: (opKeep (op==2) ka kb a b ws).map Prod.fst
theorem evalMove_sound {raw T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : (op==2)=false → a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (pro : proper (movedDecor op a b).1) (fresh : (movedDecor op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove (cap,ws.length,ws,preCov ws,pools,links) op a b (movedDecor op a b) ka kb = true) :
    Impossible T (cap-1) (moveFront ws op a b ka kb).toFinset := by
  let z := movedDecor op a b
  let rest := opKeep (op==2) ka kb a b ws
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := keep_sub _ _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : properB z.1 = true := by simpa [properB,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,len_keep _ _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k t hk h
  have hsz := (live_size h).2
  change child.toFinset.card + t ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold evalMove at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := cover_required h hk ndc (pair_sep pairs)
  have ce : cap-1+1=cap := by omega
  rw [ce] at sep
  let d := child.length==cap
  have g : (coverage d rest).1 = covered d (pairSig r s) (rest.map Prod.fst) :=
    cov_word _ _ (fun v hv => faith _ (sub.subset hv))
  have rz := rest_coverage ha hb (op==2) ka kb d ne
  have hf := moved_faithful (faith _ ha) (faith _ hb) op
  have deq : decide (child.length=cap) = (child.length==cap) := by by_cases he : child.length=cap <;> simp [he]
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 512 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 512) = false := by simp [sep]
  change (if (_ != _) then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  have val := moved_full op a b
  change z.1 = _ at val
  change Live T k t child.toFinset at h
  have nd' := ndc
  change (z.1::rest.map Prod.fst).Nodup at nd'
  change Live T k t (z.1::rest.map Prod.fst).toFinset at h
  rw [val] at nd' h
  exact closeChild_sound pv lv nd' test k t hk h


def testPair (ctx : NodeContext) (a b : Decor) (d : Bool) :=
  let op := if d then 1 else 0
  let z := movedDecor op a b
  let attempt := evalMove ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
  let z := movedDecor 2 a a
  evalMove ctx 2 a a z false false && evalMove ctx 2 a a z true true &&
    bs.all (fun b => testPair ctx a b false && testPair ctx a b true)
def testAll (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow ctx a bs && testAll ctx bs

theorem all_unary {ctx ws} (h : testAll ctx ws=true) {a : Decor} (ha : a∈ws) (keep : Bool) :
    evalMove ctx 2 a a (movedDecor 2 a a) keep keep=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow] at h
    rcases List.mem_cons.mp ha with rfl | hm
    · cases keep
      · exact h.1.1.1
      · exact h.1.1.2
    · exact ih h.2 hm

theorem all_binary {ctx ws} (h : testAll ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) (d : Bool) : testPair ctx a b d=true ∨ testPair ctx b a d=true := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [testAll,Bool.and_eq_true,testRow,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      left
      cases d <;> first | exact (h.1.2 b bm).1 | exact (h.1.2 b bm).2
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · right
        cases d <;> first | exact (h.1.2 a haTail).1 | exact (h.1.2 a haTail).2
      · exact ih h.2 haTail hbTail

theorem testPair_at {ctx a b d} (h : testPair ctx a b d = true) (ka kb : Bool) :
    evalMove ctx (if d then 1 else 0) a b (movedDecor (if d then 1 else 0) a b) ka kb = true := by
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
    (ha : a ∈ ws) (hb : b ∈ ws) (un ka kb : Bool) (v : Sig) :
    v ∈ (opKeep un ka kb a b ws).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (un=true ∨ v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (delOne_sub ws a ka)
  cases un <;> simp only [opKeep,Bool.false_eq_true,ite_false,ite_true,delTwo,List.mem_map,
    mem_delone wn,mem_delone dn,or_false,false_or,true_or,and_true] <;> constructor
  all_goals
    first
    | rintro ⟨w,hw,rfl⟩
      first
      | exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (unique_value nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (unique_value nd hw.1.1 hb eq)) id⟩
      | exact ⟨⟨_,hw.1,rfl⟩,hw.2.imp (fun ne eq => ne (unique_value nd hw.1 ha eq)) id⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
      exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩
    | rintro ⟨⟨w,hm,rfl⟩,h1⟩
      exact ⟨w,⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩

theorem unary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a : Decor} (ha : a∈ws)
    (keep : Bool) :
    (moveFront ws 2 a a keep keep).toFinset = (childOne (ws.map Prod.fst) a.1 keep).toFinset := by
  ext v
  simp only [moveFront,childOne,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha ha,keep_mem,nd.mem_erase_iff,movedDecor,codeDecor,dneg,ite_true,
    Nat.reduceBEq,true_or,and_true]
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  by_cases e : v=a.1 <;> cases keep <;> simp_all

theorem binary_front {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d ka kb : Bool) :
    (moveFront ws (if d then 1 else 0) a b ka kb).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv := List.mem_map_of_mem (f:=Prod.fst) hb
  cases d <;> simp only [moveFront,childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    kept_value nd ha hb,keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,movedDecor,codeDecor,dbin,
    Bool.false_eq_true,Nat.reduceBEq,ite_true,ite_false,false_or]
  all_goals by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all

theorem childTwo_swap (v : List Sig) (nd : v.Nodup) (a b : Sig) (d ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a d kb ka).toFinset := by
  ext x
  simp only [childTwo,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    keep_mem,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,bin_comm d b a]
  tauto

theorem node_sound {raw T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, ValidPool raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → Impossible T (cap-1) (List.toFinset xs))
    (checks : testAll (cap,ws.length,ws,preCov ws,pools,links) ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k t hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    cases h
    exact out (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply enum_step nd out
  · intro v hv keep fresh pro len
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
    have hf := unary_front nd ha keep
    rw [←hf]
    exact evalMove_sound pairs faith nd ha ha (by simp) hc' pv lv pro fresh (all_unary checks ha keep)
  · intro a ha b hb d ka kb ne fresh pro len
    obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
    obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
    have ab : a≠b := fun e => ne (congrArg Prod.fst e)
    have one (a b : Decor) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
        (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
        (test : testPair (cap,ws.length,ws,preCov ws,pools,links) a b d = true) :
        Impossible T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
      rw [←binary_front nd aa bb ne']
      have eq : (movedDecor (if d then 1 else 0) a b).1 = bin d a.1 b.1 := by cases d <;> rfl
      exact evalMove_sound pairs faith nd aa bb (fun _ e => ne' (congrArg Prod.fst e)) hc' pv lv
        (eq ▸ pr) (eq ▸ fr) (testPair_at test ka kb)
    rcases all_binary checks haW hbW ab d with hh | hh
    · exact one a b haW hbW ne ka kb pro fresh hh
    · rw [childTwo_swap _ nd]
      exact one b a hbW haW (Ne.symm ne) kb ka (bin_comm d a.1 b.1 ▸ pro)
        (bin_comm d a.1 b.1 ▸ fresh) hh


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
theorem rotate_excluded {T n} {ws : List Sig} (hi : Impossible T n ws.toFinset)
    (p : List Move) (ok : autoOK T p = true) : Impossible T n (ws.map (movedWord p.reverse)).toFinset := by
  simp only [autoOK,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (movedRow p) := fun r => ⟨movedRow p.reverse r,composed_id ok.2 r⟩
  intro k t hk h
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
  exact hi k t hk run

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
  let row := (h/nb+sh)%slots
  let word := packedAt data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots)%16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


inductive IndexTree (α : Type) where
  | leaf (items : List α)
  | fork (pivot : Nat) (left right : IndexTree α)
def IndexTree.read {α} : IndexTree α → Nat → Option α
  | .leaf xs,i => xs[i]?
  | .fork pivot a b,i => if i<pivot then a.read i else b.read (i-pivot)
def IndexTree.values {α} : IndexTree α → List α
  | .leaf xs => xs
  | .fork _ a b => a.values ++ b.values
theorem IndexTree.read_mem {α} (tree : IndexTree α) {i x} (e : tree.read i=some x) :
    x ∈ tree.values := by
  induction tree generalizing i with
  | leaf xs => exact List.mem_of_getElem? e
  | fork pivot a b ia ib =>
    simp only [IndexTree.read] at e
    split at e
    · exact List.mem_append_left _ (ia e)
    · exact List.mem_append_right _ (ib e)

abbrev ExtraFactory := Nat → Nat → List Decor → Nat → Nat → Option BoundPool
def noFactory : ExtraFactory := fun _ _ _ _ _ => none
def FactorySound (m : Nat) (f : ExtraFactory) := ∀ ops d bank idx paid c,
  f ops d bank idx paid = some c → ValidPool (vars m) (chartGoal m) c
theorem noFactorySound (m : Nat) : FactorySound m noFactory := by
  intro ops d bank idx paid c h
  contradiction

structure Forest where
  mask : Nat
  cap : Nat
  samples : Nat → Bits × Bits
  cols : IndexTree ColumnInfo
  autos : Array (List Nat)
  levels : Nat → Packing
  index : Nat → Nat → Option (Nat × Nat)
  bonus : ExtraFactory
  safe : FactorySound mask bonus

def wiresOf (g : Forest) :=
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 512) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 512) (hq : chartSamples m q = 0) :
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
  match g.bonus ops d bank idx paid with
  | some c => some c
  | none => (g.cols.read idx).bind fun ci =>
      materialize (vars g.mask) (chosenSteps bank ops paid d) (subcube ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : buildRule g ops depth bank i paid = some c) :
    ValidPool (vars g.mask) (targetOf g) c := by
  unfold buildRule at h
  cases eb : g.bonus ops depth bank i paid with
  | some c' =>
    rw [eb] at h
    cases h
    exact g.safe _ _ _ _ _ _ eb
  | none =>
      rw [eb] at h
      cases e : g.cols.read i with
      | none => simp [e] at h
      | some ci =>
        simp only [e,Option.bind_some] at h
        apply materialize_sound _ h
        exact cols ci (g.cols.read_mem e)

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
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (earlier : ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset)
    {pair out} (h : linkedSet g k pair = some out) :
    Impossible (targetOf g) k out.toFinset := by
  unfold linkedSet at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact rotate_excluded (earlier _ (by omega)) _ (names _ (by simpa using Array.mem_of_getElem? e))

def extra3853 (g : Forest) (k tag : Nat) : List (Nat × Nat) :=
  []
def ifUseful3853 {α} (flag : Bool) (xs : List α) : List α :=
  if flag then xs else []
theorem ifUseful3853_mem {α} {flag : Bool} {x : α} {xs : List α} :
    x ∈ ifUseful3853 flag xs → x ∈ xs := by
  cases flag <;> simp [ifUseful3853]

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
  let ls := fun tag => ifUseful3853 (iw != 63 || nl != 0)
    (((g.index k tag).bind (linkedSet g (k-1))).toList ++ (extra3853 g k tag).filterMap (linkedSet g (k-1)))
  decide values.Nodup && !(values.contains (targetOf g)) &&
    (if k=0 then true else testAll (k,ws.length,ws,preCov ws,rules,ls) ws)

theorem nodeVerified_sound (g : Forest) (k i : Nat)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols.values, Slice (vars g.mask) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos.toList, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (checked : nodeVerified g k i = true) : Impossible (targetOf g) k (stateSet g k i).toFinset := by
  simp only [nodeVerified,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t u lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (stateSet g 0 i).toFinset = S at h
    cases h
    exact hT (List.mem_toFinset.mp (he.symm ▸ Finset.mem_singleton_self _))
  apply node_sound (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (wires_faithful g) v
    exact (selectLive_sub _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact buildRule_sound g cols h
  · intro tag xs hx
    rcases List.mem_append.mp (ifUseful3853_mem hx) with h | h
    · have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa using h
      obtain ⟨pair,_,v⟩ := Option.bind_eq_some_iff.mp e
      exact linkedSet_sound g _ names (prior (by omega)) v
    · obtain ⟨pair,_,v⟩ := List.mem_filterMap.mp h
      exact linkedSet_sound g _ names (prior (by omega)) v


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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 512) &&
  (chartSamples g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.values.all (fun c => colCheck g.mask c prior) &&
  g.autos.toList.all (fun p => autoOK (targetOf g) (p.map swapRows))

theorem forest_all (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : checkedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
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
theorem root_index {g top prior k i ws} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g top) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_all g top prior low geom blocks _ le i idx.1

theorem lower_forest {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : checkedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (root_index low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

theorem lower_discard {g prior ci hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (ok : colCheck g.mask ci prior = true)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask)
    (nd : (vars g.mask).Nodup)
    (cut : poolCut (subcube ci.1 ci.2.1) ci.2.2.2.2 g.cap 0 (vars g.mask) (vars g.mask)=true) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (poolCut_sound (col_sound ci prior low ok) [] rfl nd cut)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def Known (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower (vars e.1) (graphGoal e.1) e.2
def extendKnown (old : List (Nat × Nat)) (L : Nat) (relabels : List (Nat × List Nat)) :=
  relabels.map (fun v => (v.1,L)) ++ old
theorem extendKnown_ok {old L m relabels} (previous : Known old)
    (main : Lower (vars m) (graphGoal m) L)
    (ok : relabels.all (fun v => relabelOK v.1 m v.2) = true) :
    Known (extendKnown old L relabels) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact relabel_of (List.all_eq_true.mp ok _ hv) main
  · exact previous e h
theorem baseKnown : Known [] := by simp [Known]
def lanePlace (v : Nat) (upper : Nat) := 2^513*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^513 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<513 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<513 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<513 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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

def fullMarks (r packed : Nat) := ((packed+r) >>> 512) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (513*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^513)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 513*(i+1)-513=513*i := by omega
      have ge : ¬513*(i+1)<513 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 512 = (a==BitVec.allOnes 512) := by
  by_cases h : a=BitVec.allOnes 512
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^512-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^512 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (513*i) =
      (f xs[i]==BitVec.allOnes 512) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^513*u+x+(2^513*v+1)=2^513*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^513 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬513*(i+1)+512<513 := by omega
      have di : 513*(i+1)+512-513=513*i+512 := by omega
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

def packedOp (full : Nat) (op : Nat) (a b : PackedSig) : PackedSig :=
  if op=2 then (full ^^^ a.1,full ^^^ a.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else (a.1 &&& b.1,a.2 &&& b.2)
theorem top_xor (a : Bits) : BitVec.allOnes 512 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 512).toNat) op
      (packedSig (fun x => (a x).2) xs) (packedSig (fun x => (b x).2) xs) =
    packedSig (fun x => (movedDecor op (a x) (b x)).2) xs := by
  by_cases un : op=2
  · simp only [packedOp,un,ite_true,packedSig,broadcast,lanes_xor,top_xor,movedDecor,codeDecor,dneg]
  · by_cases one : op=1 <;> simp [packedOp,un,one,packedSig,lanes_or,lanes_and,movedDecor,codeDecor,dbin]

def takePacked (c : PackedCov) (a b : Nat) (un ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if un then (if ka then c.1 else without1 a)
  else if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2

theorem takePacked_ok {α} (c : α → Cov) (a b : α → Bits) (xs : List α) (un ka kb : Bool) :
    takePacked (packedCov c xs) (combineLanes a xs) (combineLanes b xs) un ka kb =
    combineLanes (fun x => restCov (c x) (a x) (b x) un ka kb) xs := by
  cases un <;> cases ka <;> cases kb <;>
    simp only [takePacked,packedCov,lanes_and,lanes_or,lanes_xor,xor_meet,restCov,takeOne,takeTwo,
      Bool.false_eq_true,ite_false,ite_true]

def contextWire (c : NodeContext) (i : Nat) := c.2.2.1.getD i defaultDecor
def checkAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  evalMove c op a b (movedDecor op a b) ka kb
def combField (c : NodeContext) (d un ka kb : Bool) (op i j : Nat) :=
  let a := contextWire c i
  let b := contextWire c j
  restCov (getCov c.2.2.2.1 d) (column d a.2) (column d b.2) un ka kb |||
    column d (movedDecor op a b).2

def onMarks {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 513) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (513*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 513) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn

abbrev Batch := Nat × Nat × Nat × List PackedSig × PackedCov × PackedCov
def makeBatch (k n : Nat) (xs : List NodeContext) : Batch :=
  (k,n,units xs.length,(List.range n).map (fun i => packedSig (fun c => (contextWire c i).2) xs),
    packedCov (fun c => c.2.2.2.1.1) xs,packedCov (fun c => c.2.2.2.1.2) xs)
def laneWire (b : Batch) (i : Nat) := b.2.2.2.1.getD i (0,0)
theorem laneWire_at (k n) (xs) {i : Nat} (h : i<n) :
    laneWire (makeBatch k n xs) i = packedSig (fun c => (contextWire c i).2) xs := by
  simp [laneWire,makeBatch,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]

def availableMasked (p : BoundPool) (m : Sig) :=
  m==zero || m==p.domain || (p.wires.map (masked p.domain)).any (fun v => v==m)
theorem available_mask (p : BoundPool) (x : Sig) :
    availableB p.domain p.wires x = availableMasked p (masked p.domain x) := rfl

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

theorem keptCount (p : Decor → Bool) (ws : List Decor) (a b : Decor) (un ka kb : Bool) :
    ws.countP p - constantLoss p a ka - constantLoss p b (un || kb) ≤
    (opKeep un ka kb a b ws).countP p := by
  have h1 := lossBound p ws a ka
  have h2 := lossBound p (delOne ws a ka) b kb
  cases un <;> simp only [opKeep,delTwo,Bool.false_eq_true,ite_false,ite_true,
    Bool.false_or,Bool.true_or] <;> first | omega | simp [constantLoss]; omega

abbrev QuickPool := BoundPool × Nat × Bool
def summarizePool (ws : List Decor) (p : BoundPool) : QuickPool :=
  (p,ws.countP (fun w => isMaskedConstant p.domain w.1),
     ws.all (fun w => availableB p.domain p.wires w.1))
def fastCost (s : QuickPool) (k : Nat) (a b : Decor) (op : Nat) (ka kb : Bool) :=
  if !s.2.2 then false else
  let p := s.1
  let un := op==2
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let z := choiceVal (movedChoice op a b)
  let zm := masked p.domain z
  let zc := isMaskedConstant p.domain z
  let cm := s.2.1 - constantLoss const a ka - constantLoss const b (un || kb) + zc.toNat
  let free := zc || zm==masked p.domain a.1 || zm==masked p.domain b.1
  decide (k+p.paid+(!free).toNat < p.bound+cm)

theorem fastCost_good {p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws)
    (h : fastCost (summarizePool ws p) k a b op ka kb=true) :
    scalarPoolCut p k ((opKeep (op==2) ka kb a b ws).map Prod.fst) (movedChoice op a b)=true := by
  let z := choiceVal (movedChoice op a b)
  let const := fun w : Decor => isMaskedConstant p.domain w.1
  let free := isMaskedConstant p.domain z || masked p.domain z==masked p.domain a.1 ||
      masked p.domain z==masked p.domain b.1
  let rest := opKeep (op==2) ka kb a b ws
  have ck := keptCount const ws a b (op==2) ka kb
  change ws.countP const - constantLoss const a ka - constantLoss const b ((op==2) || kb) ≤ rest.countP const at ck
  by_cases all : ws.all (fun w => availableB p.domain p.wires w.1)=true
  · have hav := List.all_eq_true.mp all
    have ready : free=true → availableB p.domain p.wires z=true := by
      intro f
      simp only [free,Bool.or_eq_true,beq_iff_eq] at f
      rcases f with (zc|za)|zb
      · simp only [availableB,isMaskedConstant,Bool.or_eq_true] at zc ⊢
        exact Or.inl zc
      · rw [available_mask,za,←available_mask]
        exact hav _ ha
      · rw [available_mask,zb,←available_mask]
        exact hav _ hb
    have extra : (!availableB p.domain p.wires z).toNat ≤ (!free).toNat := by
      cases hf : free <;> cases he : availableB p.domain p.wires z <;> simp_all
    have hs : (rest.map Prod.fst).all (availableB p.domain p.wires)=true := by
      apply List.all_eq_true.mpr
      intro _ hm
      obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact hav w ((keep_sub ws a b (op==2) ka kb).subset hw)
    have opOK : choiceOK p.domain p.wires (movedChoice op a b)=true := by
      simp [choiceOK,movedChoice,hav _ ha,hav _ hb]
    simp only [fastCost,summarizePool,all,Bool.not_true,Bool.false_eq_true,ite_false,decide_eq_true_eq] at h
    change k+p.paid+(!free).toNat < p.bound+(ws.countP const - constantLoss const a ka -
        constantLoss const b ((op==2)||kb)+(isMaskedConstant p.domain z).toNat) at h
    dsimp only [rest] at hs
    simp only [scalarPoolCut,hs,opOK,Bool.or_true,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
    change k+p.paid+(!availableB p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if isMaskedConstant p.domain z then 1 else 0)
    cases hc : isMaskedConstant p.domain z <;> simp [hc] at h ⊢ <;> omega
  · simp [fastCost,summarizePool,all] at h

def quickAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let a := contextWire c i
  let b := contextWire c j
  (c.2.2.2.2.1.map (summarizePool c.2.2.1)).any (fun s => fastCost s (c.1-1) a b op ka kb)

theorem quickAt_good {c i j op ka kb} (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length)
    (h : quickAt c i j op ka kb=true) : checkAt c i j op ka kb=true := by
  have mem (t) (ht : t<c.2.2.1.length) : contextWire c t ∈ c.2.2.1 := by
    simp [contextWire,List.getD_eq_getElem?_getD,ht]
  obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
  have closed := fastCost_good (mem _ hi) (mem _ hj) ok
  have cut : c.2.2.2.2.1.any (fun p => scalarPoolCut p (c.1-1)
      ((opKeep (op==2) ka kb (contextWire c i) (contextWire c j) c.2.2.1).map Prod.fst)
      (movedChoice op (contextWire c i) (contextWire c j)))=true :=
    List.any_eq_true.mpr ⟨p,hp,closed⟩
  simp only [checkAt,evalMove,closeChild,cut,Bool.or_true]
  repeat' split
  all_goals rfl

def fallbackAt (c : NodeContext) (i j op : Nat) (ka kb : Bool) :=
  (if i<c.2.2.1.length ∧ j<c.2.2.1.length then quickAt c i j op ka kb else false) ||
    checkAt c i j op ka kb
theorem fallback_sound {c i j op ka kb} (h : fallbackAt c i j op ka kb=true) :
    checkAt c i j op ka kb=true := by
  simp only [fallbackAt,Bool.or_eq_true] at h
  rcases h with h | h
  · split at h
    next yes => exact quickAt_good yes.1 yes.2 h
    next => contradiction
  · exact h
def batchMove (b : Batch) (xs : List NodeContext) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,u,v) := b
  let un := op==2
  let len := 1+(n-(if ka then 0 else 1)-(if un || kb then 0 else 1))
  if len>k then true else
    let d := len==k
    let a := laneWire b i
    let b' := laneWire b j
    let z := packedOp (r*(BitVec.allOnes 512).toNat) op a b'
    let cov := if d then v else u
    let mask := fullMarks r (takePacked cov (packedColumn d a) (packedColumn d b') un ka kb ||| packedColumn d z)
    onMarks (fun c => fallbackAt c i j op ka kb) mask xs

theorem batchMove_at (k n) (xs : List NodeContext) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n)
    (pass : batchMove (makeBatch k n xs) xs i j op ka kb=true) :
    checkAt xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if (op==2) || kb then 0 else 1))
  let d := len==k
  have eval : checkAt xs[q] i j op ka kb =
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 512 then true
      else if !properB (movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(movedDecor op (contextWire xs[q] i) (contextWire xs[q] j)).1)
      then true else closeChild xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((opKeep (op==2) ka kb (contextWire xs[q] i) (contextWire xs[q] j) xs[q].2.2.1).map Prod.fst)
        (movedChoice op (contextWire xs[q] i) (contextWire xs[q] j)) := by
    simp only [checkAt,evalMove,budget,arity,len,d,combField] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := units xs.length
    let a := laneWire (makeBatch k n xs) i
    let b := laneWire (makeBatch k n xs) j
    let cov := if d then packedCov (fun c : NodeContext => c.2.2.2.1.2) xs
            else packedCov (fun c : NodeContext => c.2.2.2.1.1) xs
    change (if len>k then true else onMarks _ (fullMarks r
       (takePacked cov (packedColumn d a) (packedColumn d b) (op==2) ka kb |||
        packedColumn d (packedOp (r*(BitVec.allOnes 512).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 512
    · apply fallback_sound
      apply marked_ok _ _ _ q hq _ pass
      rw [mark_at _ _ _ hq]
      exact beq_iff_eq.mpr hit
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


def batchPair (b : Batch) (xs : List NodeContext) (i j op : Nat) :=
  let f := batchMove b xs i j op
  f false false && f true false && f false true && f true true
def batchRow (b : Batch) (xs : List NodeContext) (i : Nat) (js : List Nat) :=
  batchMove b xs i i 2 false false && batchMove b xs i i 2 true true &&
    js.all (fun j => batchPair b xs i j 0 && batchPair b xs i j 1)
def batchRows (b : Batch) (xs : List NodeContext) : List Nat → Bool
  | [] => true
  | i::js => batchRow b xs i js && batchRows b xs js

theorem batchRows_at (k n) (xs : List NodeContext) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : batchRows (makeBatch k n xs) xs js=true) :
    testAll xs[q] (js.map (contextWire xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [batchRows,Bool.and_eq_true,batchRow,List.all_eq_true] at allRows
    simp only [List.map_cons,testAll,testRow,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    have check := @batchMove_at k n xs
    refine ⟨⟨⟨check hi hi hq budget arity allRows.1.1.1,check hi hi hq budget arity allRows.1.1.2⟩,?_⟩,
      ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    have both := allRows.1.2 j hj
    have opCheck (d : Bool) (pass : batchPair (makeBatch k n xs) xs i j (if d then 1 else 0)=true) :
        testPair xs[q] (contextWire xs[q] i) (contextWire xs[q] j) d=true := by
      simp only [batchPair,Bool.and_eq_true] at pass
      simp only [testPair,Bool.and_eq_true]
      exact ⟨⟨⟨check hi hj' hq budget arity pass.1.1.1,check hi hj' hq budget arity pass.1.1.2⟩,
        check hi hj' hq budget arity pass.1.2⟩,check hi hj' hq budget arity pass.2⟩
    exact ⟨opCheck false both.1,opCheck true both.2⟩

def runBatch (k n : Nat) (xs : List NodeContext) :=
    batchRows (makeBatch k n xs) xs (List.range n)
theorem runBatch_at {k n} {xs : List NodeContext} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hn : xs[q].2.2.1.length=n)
    (pass : runBatch k n xs=true) : testAll xs[q] xs[q].2.2.1=true := by
  have all := batchRows_at k n xs hq hb ha (List.range n) (fun _ => List.mem_range.mp) pass
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
  let ls := fun tag => ifUseful3853 (iw != 63 || nl != 0)
    (((g.index k tag).bind (linkedSet g (k-1))).toList ++ (extra3853 g k tag).filterMap (linkedSet g (k-1)))
  (k,ws.length,ws,preCov ws,rules,ls)


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
def rowCut (g : Forest) (k start n ar lo len : Nat) :=
  let xs := contexts g k start n
  let b := makeBatch k ar xs
  (List.range len).all (fun d =>
    let i := lo+d
    batchRow b xs i (List.range' (i+1) (ar-(i+1))))
theorem rowCut_at {g k start n ar lo len} (h : rowCut g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    batchRow (makeBatch k ar (contexts g k start n)) (contexts g k start n)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha

theorem rowCut_merge {g k start n ar lo a b}
    (h : rowCut g k start n ar lo a=true) (t : rowCut g k start n ar (lo+a) b=true) :
    rowCut g k start n ar lo (a+b)=true := by
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact rowCut_at h (lo+j) (by omega) (by omega)
  · exact rowCut_at t (lo+j) (by omega) (by omega)

theorem cutsRun {g k start n ar} (h : rowCut g k start n ar 0 ar=true) :
    runBatch k ar (contexts g k start n)=true := by
  let xs := contexts g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      batchRows (makeBatch k ar xs) xs (List.range' lo num)=true := by
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
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [from_context,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ runBatch_at hq hb ha hn (cutsRun h)

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

def edge10495 : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 6 && x 8) || (x 7 && x 8)
def sample10495 (r : Row) (i : Fin 9) := bit r (inputs.getD i.val zero)
theorem raw10495 : List.ofFn (fun i : Fin 9 => inputs.getD i.val zero) = vars 511 := by decide +kernel
theorem samples10495 (r : Row) : List.ofFn (sample10495 r) = (vars 511).map (bit r) := by
  rw [←raw10495,List.map_ofFn]
  rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem edge10495_table : ∀ r : Row, bit r (graphGoal 511) = edge10495 (sample10495 r) := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem conclude10495 (absent : Impossible (graphGoal 511) 13 (vars 511).toFinset) :
    ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 9 edge10495 t → 14 ≤ t := by
  intro t hs
  obtain ⟨C,hf,hsize,correct⟩ := hs
  by_contra! bad
  have hp : proper (graphGoal 511) := by unfold proper; decide +kernel
  have he : (execute C.gates (vars 511)).getD C.output zero = graphGoal 511 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates (vars 511)).getD C.output zero) = bit r (graphGoal 511)
    rw [←b_read,execute_bits _ _ _ (fun g hg => (hf g hg).1),←samples10495,edge10495_table]
    exact correct (sample10495 r)
  have hout := get_rep (execute C.gates (vars 511)) C.output
  rw [he] at hout
  obtain ⟨k,u,S,hk,run,sub⟩ := extract C.gates _ hf hp (hout.resolve_right (fun h => h hp))
  have all : ∀ a ∈ vars 511, Essential (graphGoal 511) (vars 511) a := by
    have valid : checkEssential (graphGoal 511) (vars 511) (graphPairs 511 34633300) = true := by decide +kernel
    have ident : (graphPairs 511 34633300).map Prod.fst = vars 511 := by decide +kernel
    intro a ha
    apply essential_ok valid a
    rw [ident]
    exact List.mem_toFinset.mpr ha
  have eq : S=(vars 511).toFinset := by
    ext a
    constructor
    · exact fun ha => List.mem_toFinset.mpr (sub a ha)
    · intro ha
      obtain ⟨r,s,diff,sep⟩ := all a (List.mem_toFinset.mp ha)
      exact raw_required run _ a sub r s diff sep
  rw [eq] at run
  change C.gates.length ≤ t at hsize
  exact absent k u (by omega) run
def packed324r3 (i : Nat) : Nat := 0x7
def layer324r3 : Packing := (1,0,0,63,0,0,1,packed324r3)
def samples324 : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x3f,0x49),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc7,0x92),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff24)]
def cols324 : IndexTree ColumnInfo := (.leaf [])
def levels324 : Nat → Packing
  | 3 => layer324r3
  | _ => emptyPacking
def index324 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g324 : Forest := ⟨324,3,fun j => samples324[j]?.getD (0,0),cols324,#[[]],levels324,index324,noFactory,noFactorySound 324⟩
def packed147r3 (i : Nat) : Nat := 0xf
def layer147r3 : Packing := (1,0,0,63,0,0,1,packed147r3)
def samples147 : Array (Bits × Bits) := #[(0x60fff,0x221a3),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbf060,0xa736a),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc007f,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd4a5c),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff58c10),(0x0,0x0)]
def cols147 : IndexTree ColumnInfo := (.leaf [])
def levels147 : Nat → Packing
  | 3 => layer147r3
  | _ => emptyPacking
def index147 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g147 : Forest := ⟨147,3,fun j => samples147[j]?.getD (0,0),cols147,#[[]],levels147,index147,noFactory,noFactorySound 147⟩
def packed325r4 (i : Nat) : Nat := 0x1f
def layer325r4 : Packing := (1,0,0,63,0,0,1,packed325r4)
def samples325 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff087e0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff5b3ea),(0x0,0x0),(0xf87f,0x19923),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff007f,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6224c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80,0x84410)]
def cols325 : IndexTree ColumnInfo := (.leaf [(1,0,324,0,4)])
def levels325 : Nat → Packing
  | 4 => layer325r4
  | _ => emptyPacking
def index325 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g325 : Forest := ⟨325,4,fun j => samples325[j]?.getD (0,0),cols325,#[[]],levels325,index325,noFactory,noFactorySound 325⟩
def packed358r5 (i : Nat) : Nat := 0x3f
def layer358r5 : Packing := (1,0,0,63,0,0,1,packed358r5)
def samples358 : Array (Bits × Bits) := #[(0x0,0x0),(0xc00f003c03ff,0xd2474a1d4953),(0x33ffcfff00,0xd107441f0a),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff003c00f003ff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff24b894e292ac),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000fffc00,0x1470018b8e030),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeb82ee00300c0)]
def cols358 : IndexTree ColumnInfo := (.leaf [(0,2,324,32,5)])
def levels358 : Nat → Packing
  | 5 => layer358r5
  | _ => emptyPacking
def index358 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g358 : Forest := ⟨358,5,fun j => samples358[j]?.getD (0,0),cols358,#[[]],levels358,index358,noFactory,noFactorySound 358⟩
def packed179r4 (i : Nat) : Nat := 0x1f
def layer179r4 : Packing := (1,0,0,63,0,0,1,packed179r4)
def samples179 : Array (Bits × Bits) := #[(0xb303f3c0ff,0x1128b1d253),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff4dfc0cffc0,0x51c6447ca),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8e000f00ff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8e924e24ac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000fff00,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0a28bb830),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeac3002020),(0x0,0x0)]
def cols179 : IndexTree ColumnInfo := (.leaf [])
def levels179 : Nat → Packing
  | 4 => layer179r4
  | _ => emptyPacking
def index179 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g179 : Forest := ⟨179,4,fun j => samples179[j]?.getD (0,0),cols179,#[[]],levels179,index179,noFactory,noFactorySound 179⟩
def packed155r4 (i : Nat) : Nat := 0x3f
def layer155r4 : Packing := (1,0,0,63,0,0,1,packed155r4)
def samples155 : Array (Bits × Bits) := #[(0x6820ffff,0x28a21aa3),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9b03f0660,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8b1a7366a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe3fc00780,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa39c6378a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00007ff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc514a55c),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800,0x54618c010),(0x0,0x0)]
def cols155 : IndexTree ColumnInfo := (.leaf [(2,0,153,0,4)])
def levels155 : Nat → Packing
  | 4 => layer155r4
  | _ => emptyPacking
def index155 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g155 : Forest := ⟨155,4,fun j => samples155[j]?.getD (0,0),cols155,#[[]],levels155,index155,noFactory,noFactorySound 155⟩
def packed341r5 (i : Nat) : Nat := 0x104813048100401007cca8794280fe44fd43fd41fd31be44de33f611
def layer341r5 : Packing := (7,1,3,63,0,6,1,packed341r5)
def keys341k6 (i : Nat) : Nat := 0x104000000005bb400000000005d0000010019805c
def packed341r6 (i : Nat) : Nat := 0x6a47f
def layer341r6 : Packing := (1,0,3,63,0,0,1,packed341r6)
def samples341 : Array (Bits × Bits) := #[(0x80301fcf01ff,0x891142c72493),(0x0,0x0),(0xdfe033ff80,0x350e1910f8a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00e0003c01ff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff52ea9538c96c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00003ffe00,0x19c03062e7030),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe60ac18008040)]
def cols341 : IndexTree ColumnInfo := (.fork 2 (.leaf [(0,16,324,1,5),(16,0,325,0,5)]) (.leaf [(4,0,337,0,4),(64,0,277,0,4),(1,16,324,0,4)]))
def levels341 : Nat → Packing
  | 5 => layer341r5
  | 6 => layer341r6
  | _ => emptyPacking
def index341 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 29 0 7 3 0 keys341k6
  | _ => fun _ => none
def g341 : Forest := ⟨341,6,fun j => samples341[j]?.getD (0,0),cols341,#[[]],levels341,index341,noFactory,noFactorySound 341⟩
def packed391r5 (i : Nat) : Nat := 0x3f
def layer391r5 : Packing := (1,0,0,63,0,0,1,packed391r5)
def samples391 : Array (Bits × Bits) := #[(0x907f9c1f,0x191238c43),(0x20e060e7e0,0x31e972a672),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ff80f800,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc5b386f94a),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc60204518c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000,0x384c580210)]
def cols391 : IndexTree ColumnInfo := (.leaf [(2,0,389,0,5)])
def levels391 : Nat → Packing
  | 5 => layer391r5
  | _ => emptyPacking
def index391 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g391 : Forest := ⟨391,5,fun j => samples391[j]?.getD (0,0),cols391,#[[]],levels391,index391,noFactory,noFactorySound 391⟩
def packed453r4 (i : Nat) : Nat := 0x84f1b305490f1824303009e5825550e7561955429d584544ca7960151329b58a555066d62151319e580544c65d63955409758c544827561151209758c544426d6215110
def layer453r4 : Packing := (12,3,3,63,0,7,1,packed453r4)
def keys453k5 (i : Nat) : Nat := 0x855a4106f892509ba900000000a7c30014700e
def packed453r5 (i : Nat) : Nat := 0x82000200862884808690a0004008618828086a0a000610840892009620801882082250025842000000000000bc5cad966b056aa94e9f4ba3d0e84409e4e26930978b6532590c7638180a040180a8481e0c0481806006f95644bea9c897d52912faa3225f54244bf2aa877e5550afcaa995f55132be2a265dd434cbda84995f95541bf2aa637d544c6f8a898f750d31faa0a637e55502fcaa905f55120be2a241ed42483f280905f95510beaa2217c54443ea82887e50110cf22467ae4488b9c67116d91211eb19c23ba44803d445007c84600
def layer453r5 : Packing := (37,2,3,63,0,9,1,packed453r5)
def keys453k6 (i : Nat) : Nat := 0x21a41f5500297570d195000c744994899208000029f7834ed43a4f301800000f8c000000007948a11c354c0083fa2e1ac500000f281b0014000056f2c002364100121108043046400031
def packed453r6 (i : Nat) : Nat := 0x32109085633048d5223048d5222158d5225488215852148561b2a08e806e604e4032281e140a00fe44fd43fd42fd32fd41fd31fd40fd20fd10be44de33ee22f611fa00
def layer453r6 : Packing := (14,1,3,63,0,8,1,packed453r6)
def keys453k7 (i : Nat) : Nat := 0xa1006c0000060000000000000000008529a7007b0000c400a20000d8001d00730000000000000000c09a00
def packed453r7 (i : Nat) : Nat := 0x1645f
def layer453r7 : Packing := (1,0,3,63,0,0,1,packed453r7)
def samples453 : Array (Bits × Bits) := #[(0x2040fcfff80,0xe2c61c50f8a),(0x0,0x0),(0x10007f03301ff,0x1244cb2932493),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03f8003c01ff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe4ab1452c492c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00003ffe00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff70c1863a7030),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000,0x810208008040)]
def cols453 : IndexTree ColumnInfo := (.fork 3 (.leaf [(1,0,452,0,5),(4,0,449,0,5),(64,0,389,0,5)]) (.leaf [(128,0,325,0,5),(68,0,385,0,4),(129,0,324,0,4)]))
def levels453 : Nat → Packing
  | 4 => layer453r4
  | 5 => layer453r5
  | 6 => layer453r6
  | 7 => layer453r7
  | _ => emptyPacking
def index453 : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 4 18 4 8 4 0 keys453k5
  | 6 => lookupWord 12 53 5 10 6 0 keys453k6
  | 7 => lookupWord 4 43 0 8 4 0 keys453k7
  | _ => fun _ => none
def g453 : Forest := ⟨453,7,fun j => samples453[j]?.getD (0,0),cols453,#[[]],levels453,index453,noFactory,noFactorySound 453⟩
def packed215r5 (i : Nat) : Nat := 0x7f
def layer215r5 : Packing := (1,0,0,63,0,0,1,packed215r5)
def samples215 : Array (Bits × Bits) := #[(0x9326700ff0fcc03fff,0x110230a0b05cc49513),(0x31cdb9ff00ccf003300,0x1144a91f1eccf0db33a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc60e3e0000f0ffffc00,0x420e3e464650551fc4a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80fc00000ff0003fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80fc0d4d4fa0392aec),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000fffffc000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbdf0009898afaae00b0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeeab54e0e00003000c0),(0x0,0x0)]
def cols215 : IndexTree ColumnInfo := (.leaf [(0,4,147,64,5)])
def levels215 : Nat → Packing
  | 5 => layer215r5
  | _ => emptyPacking
def index215 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g215 : Forest := ⟨215,5,fun j => samples215[j]?.getD (0,0),cols215,#[[]],levels215,index215,noFactory,noFactorySound 215⟩
def packed359r6 (i : Nat) : Nat := 0x7f
def layer359r6 : Packing := (1,0,0,63,0,0,1,packed359r6)
def samples359 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff92010e403ffcccc03300,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9237064791fccccdb33a),(0x1c0033803000ff003fff,0x1c921392b4a05f149553),(0x1c3ffc00f0ffffc00,0x742c1c0650541fc0a),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe001fc00000ff0003fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe125ec25094fa0292aac),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000fffffc000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb6380006018afa8e0030),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000,0x49c0b9382e00003000c0)]
def cols359 : IndexTree ColumnInfo := (.leaf [(0,2,325,32,6)])
def levels359 : Nat → Packing
  | 6 => layer359r6
  | _ => emptyPacking
def index359 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g359 : Forest := ⟨359,6,fun j => samples359[j]?.getD (0,0),cols359,#[[]],levels359,index359,noFactory,noFactorySound 359⟩
def packed187r6 (i : Nat) : Nat := 0x90ff
def layer187r6 : Packing := (1,0,2,63,0,0,1,packed187r6)
def samples187 : Array (Bits × Bits) := #[(0xc60d0101fccf301fff,0x420515142c47324a93),(0x1093601fe0333fff980,0x1160d0e191150f98a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe71c7fe0003c3c01e00,0x251473e3c7bc3c6de3a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81f8000003fc001fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81f8a8a953b80c956c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000003ffffe000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00b0b162eeaf0070),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdaca8c0c18000080040),(0x0,0x0)]
def cols187 : IndexTree ColumnInfo := (.leaf [(8,0,179,0,5),(1,16,170,0,4),(2,32,153,0,4)])
def levels187 : Nat → Packing
  | 6 => layer187r6
  | _ => emptyPacking
def index187 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g187 : Forest := ⟨187,6,fun j => samples187[j]?.getD (0,0),cols187,#[[]],levels187,index187,noFactory,noFactorySound 187⟩
def packed486r7 (i : Nat) : Nat := 0x7f
def layer486r7 : Packing := (1,0,0,63,0,0,1,packed486r7)
def samples486 : Array (Bits × Bits) := #[(0x0,0x0),(0x20060078013fff3c03ff,0x28668a3a3011471d294b),(0x24000019ffecb00cfff00,0x2412012885a4b12444f12),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb801801e0070c00f003ff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb931931c4c70cb0e2c2b4),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc001ffe0007f000fffc00,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc024a2c00a5b024b8b028),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000007ffff000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec3803000c7ee3800c030),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000,0x13c15c1770000c00300c0)]
def cols486 : IndexTree ColumnInfo := (.leaf [(32,0,454,0,7)])
def levels486 : Nat → Packing
  | 7 => layer486r7
  | _ => emptyPacking
def index486 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g486 : Forest := ⟨486,7,fun j => samples486[j]?.getD (0,0),cols486,#[[]],levels486,index486,noFactory,noFactorySound 486⟩
def packed423r7 (i : Nat) : Nat := 0x7f
def layer423r7 : Packing := (1,0,0,63,0,0,1,packed423r7)
def samples423 : Array (Bits × Bits) := #[(0x21c80ffb7380ff980,0xe0c8643931860f98a),(0x2006700c049cff01fff,0x2842722d1014a344aa3),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe40387ff0071f0001e00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe42e858f0771f162de1a),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff803f800007e00001fff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff92bd84c267e054a955c),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000007fffffe000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec300008046ca1830010),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000,0x13c17270b800060c0060)]
def cols423 : IndexTree ColumnInfo := (.leaf [(4,0,419,0,7)])
def levels423 : Nat → Packing
  | 7 => layer423r7
  | _ => emptyPacking
def index423 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g423 : Forest := ⟨423,7,fun j => samples423[j]?.getD (0,0),cols423,#[[]],levels423,index423,noFactory,noFactorySound 423⟩
def packed427r7 (i : Nat) : Nat := 0x7f
def layer427r7 : Packing := (1,0,0,63,0,0,1,packed427r7)
def samples427 : Array (Bits × Bits) := #[(0x67fff8e8080ff980,0x622a878686860f98a),(0x501999801300ff01fff,0x542899a20322a344aa3),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe601e1e00e3ff0001e00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe6c7e1e66a3e766cde6a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff801fe000fc000001fff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8957604cfc5454a955c),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000fffffffe000,0x8180000858181830010),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7e1dd570006060c0060)]
def cols427 : IndexTree ColumnInfo := (.leaf [(8,0,419,0,7)])
def levels427 : Nat → Packing
  | 7 => layer427r7
  | _ => emptyPacking
def index427 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g427 : Forest := ⟨427,7,fun j => samples427[j]?.getD (0,0),cols427,#[[]],levels427,index427,noFactory,noFactorySound 427⟩
def packed407r6 (i : Nat) : Nat := 0x41ca100a830c4114e6208028010030418389cc1c8e80e4838703203898e1801ddbe9f9489745f4a35200b00feaa7f543fa817e55df227754fba87ed42faa8fb483ea21fa00
def layer407r6 : Packing := (12,1,4,63,0,8,1,packed407r6)
def keys407k7 (i : Nat) : Nat := 0xa50000000048a11a5bb9000000000000c607300000f200000000f4000000000000a30000
def packed407r7 (i : Nat) : Nat := 0x8762109bf
def layer407r7 : Packing := (1,0,4,63,0,0,1,packed407r7)
def samples407 : Array (Bits × Bits) := #[(0xe40ff26703ffff,0x1024243023083543),(0x440cb80c0db9fc0cc0,0x463cba6e64a99e6cea),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff880f3ff00e3e000f00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff88b52cf0ee3e596f1a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00fc0000fc0000fff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2afc2c2cfc0d34abc),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000ffffff000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff98c000808b54618010),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000,0x670ad30b0000820020)]
def cols407 : IndexTree ColumnInfo := (.fork 4 (.leaf [(2,0,405,0,6),(4,0,403,0,6),(16,0,391,0,6),(0,2,277,128,5)]) (.fork 2 (.leaf [(0,4,147,256,5),(0,16,390,1,5)]) (.leaf [(1,16,390,0,4),(128,2,277,0,4),(256,4,147,0,4)])))
def levels407 : Nat → Packing
  | 6 => layer407r6
  | 7 => layer407r7
  | _ => emptyPacking
def index407 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 4 37 0 8 4 0 keys407k7
  | _ => fun _ => none
def g407 : Forest := ⟨407,7,fun j => samples407[j]?.getD (0,0),cols407,#[[]],levels407,index407,noFactory,noFactorySound 407⟩
def packed455r8 (i : Nat) : Nat := 0x7f
def layer455r8 : Packing := (1,0,0,63,0,0,1,packed455r8)
def samples455 : Array (Bits × Bits) := #[(0x480901ff27380ff980,0x1c8590c87231860f98a),(0x40700e018039cff01e00,0x61f45e8dc6294c78de4a),(0x80000ffe00c1f0001fff,0x84809b160a41f1224a93),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff007ff00000fe00001fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0959602814be0244952c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000ffffffe000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8e01803018d4a3870030),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000,0x702604c1600004080040)]
def cols455 : IndexTree ColumnInfo := (.leaf [(2,0,453,0,8)])
def levels455 : Nat → Packing
  | 8 => layer455r8
  | _ => emptyPacking
def index455 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g455 : Forest := ⟨455,8,fun j => samples455[j]?.getD (0,0),cols455,#[[]],levels455,index455,noFactory,noFactorySound 455⟩
def packed375r8 (i : Nat) : Nat := 0xff
def layer375r8 : Packing := (1,0,0,63,0,0,1,packed375r8)
def samples375 : Array (Bits × Bits) := #[(0x4090000c30e4003fff0f303f300033cc003ffff,0x4090a50410242a90ab073017314a11cc5495153),(0xce00030ccb8003000303f33c000ccfffff3000,0xce463104cb919b466101733c4c6445531f34ca),(0xc70f3fffc000c3c3c3fffff0f0003c000,0xf45052c07c01e414141501ff0f00dbc03a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8f0000f80fc0000000fc03fc0000ff00003ffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8f0d4af80fc3550d54f803e80e94ee03a92aeac),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000fff000000000fffc000000ffffffc0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0098cefb002660998efe8000b18bbaace00b30),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000ffffffffff00000000000,0xd5b1f00000007801e0bebebea3e00000f0003c0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2a4e00baead3802e000000000c0000030000c00)]
def cols375 : IndexTree ColumnInfo := (.leaf [(0,2,341,32,8)])
def levels375 : Nat → Packing
  | 8 => layer375r8
  | _ => emptyPacking
def index375 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g375 : Forest := ⟨375,8,fun j => samples375[j]?.getD (0,0),cols375,#[[]],levels375,index375,noFactory,noFactorySound 375⟩
def packed494r7 (i : Nat) : Nat := 0x810000100500400008019109e365478c121802ff3bacb9f99a55d7ccd2273e5591377332c5eb91162deccd08f7655847db22423f958a11
def layer494r7 : Packing := (10,2,4,63,0,7,1,packed494r7)
def keys494k8 (i : Nat) : Nat := 0x182500022cf9ee400008958040154002
def packed494r8 (i : Nat) : Nat := 0x31071a9e620d6a8d513acc3246a91c2baa122a4c3246aa1d241c6aa18c38d542c6b1551146b12e8a45658d629e44dd4cb511f8be4f1f8bc2000ff99bfd65ff593fd54ff587fd51ff506fe66df957be44fb58bf611
def layer494r8 : Packing := (12,1,4,63,0,9,1,packed494r8)
def keys494k9 (i : Nat) : Nat := 0xb0239b00000000000000c70072e15500692448160000aa8004
def packed494r9 (i : Nat) : Nat := 0x10862b2ff
def layer494r9 : Packing := (1,0,4,63,0,0,1,packed494r9)
def samples494 : Array (Bits × Bits) := #[(0x0,0x0),(0x24000cc0033cc000c30e400fff33cc00ffff,0x25050cd0911cd0a0410250a50b11cd125513),(0x1080000000ccffff30ccb800c00ccffffcc00,0x1082300023445427104cb846c46445447cc4a),(0x23000cf000f0f000c70f3fff000f0f000f000,0x2330fcf31bf0f31e45052f1f31ef0f336f33a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbc000f0000ff0000f80fc000000ff0000ffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbc26af0272ee0274f80fc2d42d4ee02e4aaec),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000fffff000000fff00000000ffffff0000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc004c5545c000058efb00098098bba8b800b0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000fffffffffff0000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd487000060000060baead0e08e00000c000c0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000,0x2b780aab80bbab80000003003000003000300)]
def cols494 : IndexTree ColumnInfo := (.fork 6 (.fork 3 (.leaf [(0,32,460,2,8),(8,0,486,0,8),(0,8,358,128,7)]) (.leaf [(4,0,490,0,7),(64,0,430,0,7),(2,32,460,0,7)])) (.fork 3 (.leaf [(128,0,358,0,6),(256,0,238,0,6),(128,8,358,0,6)]) (.leaf [(4,64,170,256,5),(256,4,170,64,5),(256,64,170,4,5)])))
def levels494 : Nat → Packing
  | 7 => layer494r7
  | 8 => layer494r8
  | 9 => layer494r9
  | _ => emptyPacking
def index494 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 3 19 2 8 4 0 keys494k8
  | 9 => lookupWord 4 23 4 8 4 0 keys494k9
  | _ => fun _ => none
def g494 : Forest := ⟨494,9,fun j => samples494[j]?.getD (0,0),cols494,#[[]],levels494,index494,noFactory,noFactorySound 494⟩
def packed439r8 (i : Nat) : Nat := 0xff
def layer439r8 : Packing := (1,0,0,63,0,0,1,packed439r8)
def samples439 : Array (Bits × Bits) := #[(0x30c3900ffd5b26700ff33cc03fff,0x14104090a42c090230a0b11cc49513),(0x4400c332e00c02a4db9ff00ccffff300,0x450c4132e46d18004a9474644551f34a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe488031c3cfff00338e3e0000f0f003c00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe4885d1414b1f07b38e3e2e2ef0f0dbc3a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8f003e03f000003c0fc00000ff0003fff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8f34be03f0d4353c0fc0e4e4ee0392aec),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0003ffc0000003ff0000000fffffc000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0253bec0098263ff000a8a8bbaae00b0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000003fffffffff000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed98600000010043f6b543030000080020),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000,0x126782ebab4e0b8000000c0c00003000c0)]
def cols439 : IndexTree ColumnInfo := (.leaf [(4,0,435,0,8)])
def levels439 : Nat → Packing
  | 8 => layer439r8
  | _ => emptyPacking
def index439 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g439 : Forest := ⟨439,8,fun j => samples439[j]?.getD (0,0),cols439,#[[]],levels439,index439,noFactory,noFactorySound 439⟩
def packed431r8 (i : Nat) : Nat := 0xff
def layer431r8 : Packing := (1,0,0,63,0,0,1,packed431r8)
def samples431 : Array (Bits × Bits) := #[(0x870e4f901ff91ba501380ff99980,0x383064590c87909a50d1860f9998a),(0x48018338ce0180024c601cff01fffff,0x4a108138ce45a2000c6454a344aaaa3),(0x2100e1c3f0ffe00e38f801f0001e1e00,0x210ba142d0b1e0ee38f82df162de1e1a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc600fe03ff00000fc0fffe00001fe000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc663fe03ff0cc66b40efce066cdfe06a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800fffc0000000fff000000001fffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff84af7ec000984cfff00a8054a95555c),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000fffffffffffe00000,0x290c000000010084b61030a183000010),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd6f05cb92a4e17000000c0060c000060)]
def cols431 : IndexTree ColumnInfo := (.leaf [(4,0,427,0,8)])
def levels431 : Nat → Packing
  | 8 => layer431r8
  | _ => emptyPacking
def index431 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g431 : Forest := ⟨431,8,fun j => samples431[j]?.getD (0,0),cols431,#[[]],levels431,index431,noFactory,noFactorySound 431⟩
def packed415r8 (i : Nat) : Nat := 0xff
def layer415r8 : Packing := (1,0,0,63,0,0,1,packed415r8)
def samples415 : Array (Bits × Bits) := #[(0xc393e40ff009a502703ffffff,0x10009164243000a50a308355543),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9240cb2e3380c0936c6039fc0cccc0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9263cb2e33a6e6912c69a99e6cccea),(0x2080f3cfc3ff00e38f803e000f0f00,0x208b514b42cf0ee38f85be596f0f1a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc300fc0ffc0000fc0fffc0000ff000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc323fc0ffc2626b40ef9c09a6ff02a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00fff0000000fff00000000fffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc2afff0002c2cfff00d00d34aaabc),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000fffffffffff00000,0x248c00000008084ad1061461800010),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdb70aeb4a930b00000080082000020)]
def cols415 : IndexTree ColumnInfo := (.leaf [(2,0,413,0,8)])
def levels415 : Nat → Packing
  | 8 => layer415r8
  | _ => emptyPacking
def index415 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g415 : Forest := ⟨415,8,fun j => samples415[j]?.getD (0,0),cols415,#[[]],levels415,index415,noFactory,noFactorySound 415⟩
def packed487r6 (i : Nat) : Nat := 0x48f309183011fa9921d6580295b243b2c8aa52b6507658952a56c90ecb2281479951d96050295b283b2c49051e6547658120
def layer487r6 : Packing := (7,4,5,63,0,6,1,packed487r6)
def keys487k7 (i : Nat) : Nat := 0x58e44d635b3585
def packed487r7 (i : Nat) : Nat := 0x20606305901800000000c4040000000c3078010b07084410b070840180081c2e00808442c2e00808402038780260058010180160040600580103878020bc4e1e0902f8f8780483001c00700103878020bc3e1e0902f0f8780483001c00700100444396084e3c20be59313082f964820c3c20be5930f082f964820800000000804ff1f73e87b4f31e33c0774ed1d73a8734e51c7388704df1b7360694cf193318624c11772d8584ab1532905049d1372604a49311f230454850f71c83846d0d31983245f0ab130254470871001f4350570881041f02b0300540900f018024030030009fd809dd65df9809dd65bf9809dd65dfa771c165df9741c165df9721c1659fc8799a559fd859dd649fd809dd649fc87955649fd809dd549fd801d954f7880595549fd859dd629fd809dd629fc87955629fd809dd529fd801d952f7880595529fd859dd609fc8755160e7d65551609fc8754960e7d65549609fe885d950f7965581509fd851d940ef965581409fd851d920ef96558120c7d751d6669f9809dd659be885d065cbe665d065d3d655d0659ee885c865cee665c865d6d655c865cf6665c465cfa665c065d79655c0659ed829dd649ed821d9549f9801d954cbc7659154bad8219644bb58119644bb98019644e3e66956449bd849dd629bd841d9529f9801d952cec7658952bad8419622be58119622be98019622e6e6695622e79655815097d851d9409ed821d940cbc7659140cf8765814097d851d9209bd841d920cec7658920cf876581209f88759600e7a6695600eba6691200f3a5591200eea6688a00f6a5588a00
def layer487r7 : Packing := (72,3,5,63,0,11,1,packed487r7)
def keys487k8 (i : Nat) : Nat := 0x51f8e462d129260c1256cf5d834841cb448e8d674001938008736214b82c886a0a1331b4830db234c08432c00061dc52c539b8000000004500000060cdf800331a781e80502daab55a0fc1202d0053ec35ebfe3806d654d79e7873320000061c001f140071fb0800080fc22212e1cabae745aa35281302009001e2e804122818b000001614103800e14086
def packed487r8 (i : Nat) : Nat := (if i < 1 then 0x582206264200c844450c40f101a1911608618b0410b041010a146091088e10846148090480e108421163421a8c506352090c791887108b043821480a30510210182ca2c50e094651428704a328914384068b28b1858a121c2030596884802c98d165920208a005945281016512a040e0c0045091a2f28b070048a0052328a8e1a00a1c40a4652318291945081c348ca2e5880e52322340087ca208c900145002090104687005232898e2200a2430a4652118291944881c348ca2e5860e52122340087ca208490014500207010468700428487080e1659d003946c5081840c204509080f2cb08122432c292103081224328d92165143c40f2328a1034291945cb081858f291121039610823207cb08411153e523224859448e103c8ca2440d0a465172c206148ca404840e584208481f2c2104054f948489200302146902480a4461230718a20372cb904911b9652243407c0326224340dcb2e5c3148cb148cb8639196291970c7961cb8625196251962c5bc47c2cc18c04bf7be3bc8ba6b84b69b4eb2cb0aaefadbac7ac1ab4aa7a85a78a6ba49a3ca28a0d9f29de9ca9bd9b09a399698996093790e8de8a088c86a85685082e80c7ff7f27c97b57a178677275e7437216f86eb6d06c36a169468066565163662260e5f35d15a859b5805735515445305155014ca4bd4a949c48f48245944c42a41d4103ee3cc3aa3813743523453232fa2d82b629426b25e23c22f20d1e41c21b51a819418717316613d1140e40bb0a709307806404903c028014000ff8eb337fe77597ff332cbff5d165ffae4b2ffd70597ff334abff1d564ffacab27fe55593feb2aa9ff1d562ffacab17fe5558bfeb2aa5ff9dd60ffcccb07fd75583feb2ac1ff5d160ffac8b07fd54583feb92c1ff58960ffaa4b07fe66543feb22a1ff58950ffacaa07fd654837ebaccdbf1d666dfae9336fd7299b7eb84cd7f5d666bfae9335fd7299afeb84cd7f9dd65dfcccb2ff8705977f330cbdf59465bfae832dfd72197be3b4abdf99a55bf8ed2aefe66957beb2cab7f9dd64dfcccb277e55592ff3baa97f5d954bf8ecaa6fe66553beb2aa9df95554f7ac8aa7be66913deb2c89ef19644f7cab225fe7758b7f332c5df95562bfceea95fd7654afe3b2a5bf99952efacaa977e5554bf6b12a5fb99a22fdacb117ec6588bf72ac457f9dd60dfcccb06fd65583bf2aac1ef91160fdc44b05fd765437f332a1df59550f7c88a87ee22543fcb02a17f9dd40bfaeca05fc765037f332817f5d540efcaaa07bd64503deaa281fe58140bfcee905fd76482fe3b241bf99920bfaea9077e55483f6b1241fb54920ff2c0907fa66803fcb2c01fe59200ff2a9007f962803fca94016f5d065bdae432df571196fcb80cb9f99a55d7ccd2273e559137733445db95622df4cd0077a55803dd22401fa88a00 else 0xb4010b0f10b0f083468a2488a2440878310a90803230d14410384868644)
def layer487r8 : Packing := (128,2,5,63,0,12,1,packed487r8)
def keys487k9 (i : Nat) : Nat := (if i < 1 then 0xb2c00000000000000000000000000061783000000000000f080000000000000000000000000000000000000000000000268912001cd68c298000000000000000000000000000000000000000000000000000000128200000000d4400000000000000000000000000000076c000fa00000000000bf73fc00000000000000000000000000000000000000000000d10000000000000000000000000000003ae8000000000000000147449000000000000000000009a000000000005ae000000000000000000004800000000000be32e4000000000000000000000000000aa8000000000000000000000000000000000000000000000000000028200000765a6e16000000000000006a8000d54000000ea000000002922fc000000012d8000000000000000000000000000000ce00000000198c0000095200000000000001b7000f8a0000000079e018000000000000000000000000000001a1c00000001d100000000000000000000000000000017180000000000000000000564000000000028f80000000000000001844006e4000001d0800001acc0000000000000067000003f08000000000002a00000000000a7584318800833f80000000000000000000000000293000000003ac000000000000000000000000000281000000000002ea000002c2000000df5c1800000000000000000020280000000000000000000000000000017c800a36000004520000000000000000000000000000000000000000000000000000000000000000009d8000000000000012800000000000000001638000000000000045e00000000000000000000000000000000000000000000000000007c325600000000000000000150000000000000000000000000770000000000000000000167800000000000000000000000000000068c000000000000000000000000000000000000000000019f00000000000000bde000000000000000000000000000000000000000000000000000000000000000000000003f80000000000000000000325000000000001ee0000000000000000000d814ec00000000000000c7000000000000001d80000000000000000001f3400000000000000000000032d027fa795c00000000000000000000000000000000000000001f2800000000872e7000001f580047000192c000000000000000000000000000000000000005e80000000000000000000000002c500000000284000000000000000e60000000000000000000e6a00000000000000000000010c80036d001fc800000000000000000000000017c000e342f80000000000000260000000000000000036bb4c0000000000000000000001cf00076200000000000001c04006140016f4000000005f80000045bda40000000183c0000000000000000000000110000004090044 else 0x5e000000000000000000000000000000000000000000000009258b3cc0000000000000000)
def packed487r9 (i : Nat) : Nat := 0xe8c48512cc11b44b22285129b28344a6c83c48912ca89a44b20f12044b2a06912c868544b20544a6c81226912ca1206912cb1512c70c43d12cb1112c71112c611b44b27cba9b0c95baa12c873c1a4ae451c89c360f003fe66ff597fc65ff957fd64ff553fd62ff54bfd60ff543fd40ff482fe66df957be44fb88bfa00
def layer487r9 : Packing := (17,1,5,63,0,9,1,packed487r9)
def keys487k10 (i : Nat) : Nat := 0x38000e79ad900041803894a002940000000000046e480000700000000e1001b21c00410028e00000009a000000240
def packed487r10 (i : Nat) : Nat := 0x120b1ff
def layer487r10 : Packing := (1,0,5,63,0,0,1,packed487r10)
def samples487 : Array (Bits × Bits) := #[(0x248010e400fff1936e7003ffcccc00cc00,0x3e48370641e41f0912630781fcccc36cc3a),(0x1000700033800c0021c939ffc000ff000ffff,0x141472121390ad0a01402942d0a05f1125513),(0x120000001c3fff000c60e3e00000f0fffff000,0x1208c004742c27026420e3e11846505447f04a),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc0038001fc000000f80fc000000ff0000ffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc9ab84e5ec274274f80fc0b52d4fa02e4aaec),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0003fffe00000000fff00000000ffffff0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0132d8b800058058bdf00026098afa8b800b0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000fffffffffff0000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff61c000c000060060f6ad94380e00000c000c0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000,0x9e012700b9380b80000000c03000003000300)]
def cols487 : IndexTree ColumnInfo := (.fork 9 (.fork 4 (.leaf [(0,32,453,2,9),(32,0,455,0,9),(1,0,486,0,8),(4,0,483,0,8)]) (.fork 2 (.leaf [(64,0,423,0,8),(2,32,453,0,8)]) (.leaf [(0,2,325,160,7),(128,0,359,0,7),(68,0,419,0,7)]))) (.fork 4 (.leaf [(0,4,163,320,6),(0,64,163,260,6),(256,0,231,0,6),(1,2,324,160,6)]) (.fork 2 (.leaf [(129,0,358,0,6),(5,0,482,0,5)]) (.leaf [(65,0,422,0,5),(256,4,163,64,5),(256,64,163,4,5)]))))
def levels487 : Nat → Packing
  | 6 => layer487r6
  | 7 => layer487r7
  | 8 => layer487r8
  | 9 => layer487r9
  | 10 => layer487r10
  | _ => emptyPacking
def index487 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 8 3 7 3 0 keys487k7
  | 8 => lookupWord 24 86 7 11 7 0 keys487k8
  | 9 => lookupWord 42 764 2 11 7 0 keys487k9
  | 10 => lookupWord 5 41 2 9 5 0 keys487k10
  | _ => fun _ => none
def g487 : Forest := ⟨487,10,fun j => samples487[j]?.getD (0,0),cols487,#[[]],levels487,index487,noFactory,noFactorySound 487⟩
def packed471r6 (i : Nat) : Nat := 0x7102e47005a5d00589e2f803000c4f13c01a101718364b08565b08588e2f843c4713c218000901000000000000acd065308813f1b6cc5ea951a6c259147e30150903c18090300c00ced3b900b9acb9d97420173596bb120b9ae4b2dd624183595549e6c9510b22a759d949dd5358aeb120c1acaa97a35915358942cbb3b90ab8ac1974855d1715832e90ab92e2b05dc2558158140bb84ab02b02413e592a216444276b29442c4887a95916250910a3cc80ecb2aa94ad921d9645528f3203b2caa952b6507658952a56c90ecb2281479951d96050295b283b2c49051e6547658120
def layer471r6 : Packing := (24,4,5,63,0,9,1,packed471r6)
def keys471k7 (i : Nat) : Nat := 0xba04caae0894fe400aad40000000618002f5018d1429000031027f218800362a1b419eb3110a610
def packed471r7 (i : Nat) : Nat := (if i < 1 then 0x2c08103018c48288c4e18f101e104388420e210a002000921009212587979327809a5e1e0128f178433264e4e10cc9920800000038010387804a30a07138433264c4e10cc9920801787822a1250028100000000000040050010008007979323849e5c9c80b2720207041811312e1e049881b938033224c5e00cc892083138033224c4e00cc89208300100000000000000000093491e9088f28e48d68c08aa88c87686885283c8368308228147f67e07da7d47c67b079a77c75e75074a73c72e7187026e46ce6b069a68466e65864262c6165f05ca5b45a659858256c55653851a5144fe4e04ca4b449647847245c43e43042240c3f63f03ea3e43de3d03ca3bc3ae38036233c31631030a3042fe2f82f22e42de2c02b228c26626025a22c22621821220c2062001fa1f41ee1e81da1cc1c61c01b218416e15814a13c1060e00ba0b40ae08806205c05604804203c03603002a02401e01801200c0060009fd809dd65dde775cd65ddd745cd65ddd735c9659fd859dd649fd809dd649fd809dd549fd801d954f5d8359554bde8859563ddc8799953bdd8499953bdd8299953bde8859153fcc82591539fd859dd629fd809dd629fc8755162edd6458d62dde7754d62f9c7454d62edd6454d629fd809dd529fd801d952f5d83595529fc8759152f5d5458d52ddd7654d42f9d6454d42fcd5358942ef564589619fd859dd609fc8755160e7d65551609fc8754960e7d6554960df6775c560df5745c560df5725c560df677585609fd869dd509fe885d950bbd841d950bed821d9509fc87999509fc87591509fc8758950f7965581509fd859dd409fd851d9409fc87595409fc87589409fc8754940ef96558140ff181581409fd859dd209fd851d9209fc87595209fc87591209fc8755120ef96558120ff18158120ff16150120df48799910bf58499910bf58299910bf68859110fe48259110bf68858910fb48458910ef56458910bf58650910fb56450910fe56250910bd8805cd659ed829dd649ed821d9549f9801d954c7c7659554cbc7659154e3e6695644e5e6695563e9e6691163f1e5591163cdc8799953e9e66911539bd849dd629bc87911629bd841d9529f9801d952c7c7659552cec7658952ead6458942e6e66956229ec8759222eae6691222f2e5591222ece6658e22f4e5558e22f8e4458e22ece6654e22f8e4454e22eb66691161ed66658d61f964458d61ee66688961fa64488961fc56388961b74855c5609bd841d9509ed821d950c7c7659550cf87658150e79655815097d851d9409ed821d940cbc7659140cf8765814097d851d9209bd841d920cec7658920cf87658120cf48799910eb66691110ee66688910fa64488910e7a6695600eba6691200f3a5591200eea6688a00f6a5588a00faa4488a00ef26658600fb24458600fe22258600 else 0xb84262018991822a5a088001010408042c9e10a271782322010b8011120084480280000040410a03050c49102800448408042c9e10a27138230b03040f1010112185844890203e008301c083c21308301c083c212098c022646189958624300080c08203020b272387804c9c8e1e010040020b042814988080c002c8e00830180c30a02050c063130a231786303000b238020c06030c)
def layer471r7 : Packing := (135,3,5,63,0,12,1,packed471r7)
def keys471k8 (i : Nat) : Nat := 0x1694080008491f4dae8f80009ec0024d99080029a6c4c130039d2782b9666060b2875d16878096090002cf3193460002dc10bd4f400295e53be10003142cd6d8fd9cd778fcc04000484cdf5199e4982414003c5edb9459e09db00031e30550c4003df00030241dc411052d3f88cd1f064d7fcba070511045c35d8bc2f9c5020001e144d0002dd4d204cac83d48003d6c8e4003129430001d0c0024ce501c0e4a400012c81a60d9b6dd0001dfee021500015a286e81c003dcbce00a3d54003ce85440039701a895b21b47d8c20ac14f58513699417a9f88ecddbc9f1bfc41c6843c000c00c8a1980031cdd629060b4001c98000cab1e8638310000302211714158001f00200208314b50810008a1974c3649141012001300
def packed471r8 (i : Nat) : Nat := (if i < 1 then 0x2449912259126448b6449910a0911a340a4348942409424a90240902480e093863c3822c2a628382446a644582445270488e4c88b0e08b0a98b0e08b028894a88a061931e193113ca4a4a8970c98a461931c893148931619182353222c1222c122253222c0f5fbafa77b8bcb5d9ae6d71bb7cdb5ed4f685b2ad8cec235f6ae35676b05552a94d3e69af4b5a49d17287540a9f44ee270335899b4c1a5bb2bb945c9c24ab23a90fc7a23711818a5444e1f10cf85a422e0ef0638164029fa6fa37c7bd7de6cf1b7803b25d24e697203841bdcdc56d8b675accd36694b4019bccbc642b155882c115f0af35748b7b5a92d1562ab085732af5536a7952f290d46ca224f5a70933297049ca4791f88e146322ad10484b40a1f58f5a78b3ad9ce4e2e6e73629a38cbc64a3109834bc85c22d71614aaa53327e133097048823a11108604071f28ef071835c1960c285d02c61558a404f826812a090046621810207c03aa1c10d686482fc16a0ab050825c11a07f83ac1840ae04981fc0d605001e00a0028000ffceeb2ffe66597feba2cbff5c965ffae0b2ffd65593feb2ac5ff59162ffaa8b17fd6454bfeb2a85ff9dd60ffcccb07fd75583feb2ac1ff5d160ffac8b07fd54583feb92c1ff58960ffaa4b07fd42583ff3baa1ff5d950ff8eca87fe66543feba2a1ff59150ffae4a87fd62543fea12a1ff59540ffac4a07fd52503feb2a41ff59120ffaa8906fd7599b7eba4cdbf5ca66dfae1335fd7599afeba4cd7f5ca66bfae1335fe775977f332cbf75cd65efccd2adfe775937f332c9df95564fd8e4b25fe77552febb2a97f1d954dfcccaa77d65553deb22a9ef99a44f7acb227de6658feeb2ac7f759163fbaa8b1fde6654feeb22a77f9dd62dfcccb177e5558bde3a2c5bf59162f7c88b17dd6358beea9ac57f9dd52bfaeca95fc7654b7f332a5df59552efaa8a97be4454beeb1aa5fb58952bfaeca16fe6650afebaa85df95542f7ac8a17dd6350beea9a85fb58942fdccd117ed6588bf6b2445fb55222fecccb0ff564587fab12c3fd50961bfceeb06fe665837eb2ac1df95560f7c88b07ee22583fab8ac1fd58560bfceea85fd76542fe3b2a1bf99950efacaa87be44543f7112a1fe58150bfceea05fd76502fe3b281bf99940bfaeaa077e55503deb2281ef55140fdc44a07f561503fcb02817f9dd20bfaec905fc764837f332417f5d520efcaa905fd74483df22241fb58920fdaa4907f561483fcb0241fe50120feccc887f564443fab1221fd50910ff4cd007f965803fcb2401fe55200ff2c5007f952803fca14019f99a55d7ccd2273e559136f332c7d795563f3c88b1ede6654fcf222a7bb99a22edcab117ae4488be6b1c45f354e22decccb0fb644587eab1ac3f988961deccc887b644443f311221be99a00ef4ab007ba44803f511401fc58600 else 0x18870499064343010491a4a4c11c94b82392a10e0109a9888d045189298a8d044189258918f0a80848402401f20d53111a02430cc28244832141428240ca6420c224140a6449212618c9c8490a0a51a44282809cb212e18c9484b0a0a41a442828094a36424850490d87049902499187009870499120c82860209322793230e0124c8490600b9a4c8c380493212c1802a61a2a4c8490600ea51c1404e51e160909080582807a4994a3828094a402411f2100b0500f89329438034a87006910e00d421c01860a10061523070e1b261c03260e182a4c38064e1c284038140c1c58a0c14261933c380803cb924e0512a14126315170e0272c4401448a169d1170e0484e715849c99098608030c91e38a07170c9193408a110c3804c527324c23e493950c0411a340a434e95201c12064e9521325824299d3a4c1209ca97260904e52a95260932264a924c8905c4c38094b1500516205a7444c3812929c2e1c03c8449a2431e2e0504a589154a8905e1252642418280c32480e2c1c4c32464d022043f0e0131094c1708988407cd0220516260504a54b84849252870d870129620218044c2a490d101c38090d922609aa090b126a951261c0486c8860208d1a0521a5850250932548030c9193a6498649395325c32494a930ad924851628385098244f0a0a00f0e05322485064070a0c80e141901e5c9230a9962c4264b0a99138c162828493227162a4850987048a058a932064b260c0902132587009913498302409260c09021325830889330ac04e4484c384038240f1c5028b8240c9a0c5080e4c12098b062849300f904e526a640f120c50a2e4c2a49ca430e011149cc2f012912120e140e090407160a26090326831020b100e090486831020e0626090486831024b8084825292532080916261524a51f87008884a60b80444203e62895261912664a9)
def layer471r8 : Packing := (176,2,5,63,0,13,1,packed471r8)
def keys471k9 (i : Nat) : Nat := 0x316c5291d72aa1af87329a46367da4868112d4c5898001965483201ab12a22855f115e26e1e6a27e216bc001cba158000523ce61260c80021a91a0e1a0b04cf0bc914c030044d40032405721600000021be0fe42000150c01216827be97190c160a69c994f65c5eda4400000000258ac33c48cb45810a34258370dc0009461dfe30003db9c904ec07c2692294080020f3692a36c3b53c0014e1c8c82a2594c060c90b01b074000cade4c00342e553c4e4e98410f5047239c1f09d4a9e9dc78c8a539c680035495e94d9266857df923edb5513d8fc6c00fdd313588791ba080005c6e540010d183d9c34f8002d305740002b4a2e5d800066399fc5d6779959a7e12a1400257e1025986ba850a1d9780000000002700035559f59cca8ee8aaac585d1d2531e10940029ffea4607907c599b38651412ba0008206020810376000020a00000000c1b124f00020480100941c3a50028009000000d000c002180001f02241051618004
def packed471r9 (i : Nat) : Nat := 0x244e9a254a18280e0a25921267129a24153860a058289214c99c5a689444a1828120a25852267484a688603670a1a659202278609642489858699204c89c48699604889e9a25921826a25921265a689058609a9964808965909224a689448609a8964849965908264a65920225cc300b2a9a99234811d46a97a529203f0d22b8901984209000ff99bfd65ff593fd54ff58bfd52ff50bfd60ff543fd40ff482fe66df957be44f758fdd53fb88bf561fd443fa00
def layer471r9 : Packing := (20,1,5,63,0,10,1,packed471r9)
def keys471k10 (i : Nat) : Nat := 0xabd000d580800000021800000003a0bf029800007200534000000000000000000000000003ce000000000007600000b1002be0200f48000000000004600001122
def packed471r10 (i : Nat) : Nat := 0x2505204137f
def layer471r10 : Packing := (1,0,5,63,0,0,1,packed471r10)
def samples471 : Array (Bits × Bits) := #[(0x480039007ff093267007fc3f3007fff,0x284824090520b0110230502c173092a13),(0x1100670032e0060031cdb9ff80333c006600,0x1187e746f2e8f71e1144a98fc7b33c9b673a),(0x220000003cfff800c60e3e00003c3ffff800,0x22118008d4b13826420e3e2311941523f84a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbc0078003f000000f80fc000003fc0007fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbcb5785cbf0ba174f80fc0ea753e80f255ec),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0007fffc0000000fff00000003fffff8000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0262d970002c058bdf0004c262bea5c00b0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000ffffffffffc000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe638001800030060eeab54703800006000c0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000,0x19c052602b4c058000000080400000800100)]
def cols471 : IndexTree ColumnInfo := (.fork 11 (.fork 5 (.fork 2 (.leaf [(2,0,469,0,9),(16,0,455,0,9)]) (.leaf [(0,2,341,128,8),(0,16,454,1,8),(4,0,467,0,8)])) (.fork 3 (.leaf [(64,0,407,0,8),(1,0,454,0,7),(128,0,341,0,7)]) (.leaf [(1,16,454,0,7),(128,2,341,0,7),(0,4,147,320,6)]))) (.fork 5 (.fork 2 (.leaf [(0,64,147,260,6),(256,0,215,0,6)]) (.leaf [(68,0,403,0,6),(3,0,452,0,5),(4,64,147,256,5)])) (.fork 3 (.leaf [(64,4,147,256,5),(144,0,325,0,5),(256,4,147,64,5)]) (.leaf [(256,64,147,4,5),(3,16,452,0,5),(144,2,325,0,5)]))))
def levels471 : Nat → Packing
  | 6 => layer471r6
  | 7 => layer471r7
  | 8 => layer471r8
  | 9 => layer471r9
  | 10 => layer471r10
  | _ => emptyPacking
def index471 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 8 33 4 9 5 0 keys471k7
  | 8 => lookupWord 45 165 6 12 8 0 keys471k8
  | 9 => lookupWord 58 205 7 12 8 0 keys471k9
  | 10 => lookupWord 6 58 1 9 5 0 keys471k10
  | _ => fun _ => none
def g471 : Forest := ⟨471,10,fun j => samples471[j]?.getD (0,0),cols471,#[[]],levels471,index471,noFactory,noFactorySound 471⟩
def packed255r8 (i : Nat) : Nat := 0x1ff
def layer255r8 : Packing := (1,0,0,63,0,0,1,packed255r8)
def samples255 : Array (Bits × Bits) := #[(0x18301a130591b009a50009c003ffc30f33303c3f3330003333cccc003ffffff,0x8100a1100909000a50aa8c2a82ac1073330141733314a1111cccc549555153),(0x20486c1c0a024936c6000e7ffc000c303c3f3333c3c000ccccfffffff333000,0x82c1400000912c6066a419c19841014173333c3c0c64444555431f3330ca),(0xc1818060cce38e38f8000f80000030c3c3c3c3c3fffffff0f0f0f0003c3c000,0x40808020cce38e38f841ef90790790414141414155541ff0f0f0f10dbc3c43a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0e0e0f80f0fc0fc0fffff00000003f03fc03fc03fc0000ff00ff00003fc0000,0x10a0a0e8050b40b40ef1ff007f87fbf03fc03fc03fc03deff00ff00fdbfc03fa),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff000ff000fff0000000000003ffc0003fffc000000ffff0000003ffffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff000ff000fff00d5403553553ef80003ebe8000e94eeee0003a92aaaeac),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000fffff0000000000000003ffffffc0000000000ffffffffffc000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000fffff00000d9803663663befebe80000000f18bbbbaaabce0000f30),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000003fffffffffffffffff00000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbf7f7fdf00000000009e002782782fbebebebebeaaabe000000002f00000bc0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffef5e5d16aaf4b64ad10e005380380000000000000000c0000000003000000c00),(0x0,0x0)]
def cols255 : IndexTree ColumnInfo := (.leaf [(0,4,187,64,8)])
def levels255 : Nat → Packing
  | 8 => layer255r8
  | _ => emptyPacking
def index255 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,8,fun j => samples255[j]?.getD (0,0),cols255,#[[]],levels255,index255,noFactory,noFactorySound 255⟩
def packed447r6 (i : Nat) : Nat := 0x319c2f0878bf1f083000b4c180b66281945d973b7229d9258130a36680865d973a3669c8658130
def layer447r6 : Packing := (4,4,5,63,0,6,1,packed447r6)
def keys447k7 (i : Nat) : Nat := 0x240c800000002c0d00
def packed447r7 (i : Nat) : Nat := 0xcce2e18c0cce30a330b8630ec50b2f8f8a30e66c50f2f8420e660a2f8f0a303938c37304e4e30dcc920e4e10dcb939384372c483017ab251a61127a37990aa521f8b05216018017b89061176bcec9cccba4f7640865cfb3b28bb2e7cdd765cd60af64bb04b073e5d9705827bb2e43261ed97658130fe4c92c0985f364e664827ab22432e73d99021973c6e432ecb9c7765c864c27ab2243261ad88658130
def layer447r7 : Packing := (17,3,5,63,0,9,1,packed447r7)
def keys447k8 (i : Nat) : Nat := 0x448380c28d57ac00c0002404800000000000e38000000004300125b180182af817b470
def packed447r8 (i : Nat) : Nat := 0x405061ccc586324910c639121582060a0834c38647325e3c22080c0430608086253458c74b86464978f1463a1c2962451c2e31cb1090907a447181801c98f08d91002801400a007182cf306cb931e1843074c801c98558e110038b3cc56220072619638440082c39e58d95003931ac1c264c78610b1d32004002003001f3fb4e6777d7341c7f04ba6ceab2919be548ca1784604789d5721bb6b98555548499193dcea320bb2488518c33098200680d002ffa2176fbd845dbef99974fbd76592ffa2170dfd765c3f760d70bfe88582ff61d60efd76583f75cd60fed82583fb58960ff970583f75d930fee664833f9de66edd8399af760e66ebe665d36f9dd64ebe66592f7a2173bdc865cf775d973ede665cfe759173eee6658beb59162bde884c2f761d30dde774c2f721930ede664c3f358930fd9604c3bb99920dfa77803be99a00fd973803fa58a00
def layer447r8 : Packing := (41,2,5,63,0,10,1,packed447r8)
def keys447k9 (i : Nat) : Nat := 0x497c3cc364a883069048801f3785ee68d8544f00ba7cc80000349c001d2f6ae083c40000000606c60b54f8018ec1e8a001a28d0001a4eb71a4dd4a00000ea8018c6475084a00006200000
def packed447r9 (i : Nat) : Nat := 0x91a18e29cc9ca2448a38673a83a38623272e72858e18a72e78e29cc9248a38679623272e43ac8a19cb9a1ace8cc9e63ab8e29cc9a3b0e84b9e688b9cc9228672e4ed692e94493409c8ba48198781e007fd76ffccdff5c3feb05fe77dfccdef5d3deb27dd73fdac5f74c3f6907fa00
def layer447r9 : Packing := (13,1,5,63,0,9,1,packed447r9)
def keys447k10 (i : Nat) : Nat := 0xb000000000000000000000035000000ecd800aa0049000056000000d497c09200817300001c
def packed447r10 (i : Nat) : Nat := 0x62c6209e6ff
def layer447r10 : Packing := (1,0,5,63,0,0,1,packed447r10)
def samples447 : Array (Bits × Bits) := #[(0x10c38618727c803ff82c8d804d28027007fccccf333007fffff,0xa00418200122c82905804848005282a30502c4447333092aaa13),(0x92400630c19965c67003000501249b630039ff8033333fffffe66600,0x92506210409965c6721b43000004896321a943a19111155543e6668a),(0x44208018c70e1e79f87ffc006671c71c7c003e00003c3c3c3c00787800,0x442085e8450a0a296858fc1f6671c71c7c17be2f17bc3c3c3c3b78787a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff88c3001f07f01f81ff800000787e07e07fffc000003fc03fc0007f8000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff88c331ff07f01f81ff8678cf285a05a077e7c0cf67bfc03fc0db7f81ba),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0fc001ff8001ffe000000007f8007ff80000000003fffc000007fffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0fc355ff8001ffe0006d0da7f8007ff807500ea753bbb8000f25555ec),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00001fffffe000000000007ffff80000000000003fffffffff800000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00259defbf60000004e09c7ffff800005600ac562eeeeaaabc000170),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000000000000007fffffffffffffffffc000000000000000,0x55248600000000000000801057a5b25688181430180000000020000040),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffaadb7817bae5d5d6952702e000000000006000c06000000000c0000180)]
def cols447 : IndexTree ColumnInfo := (.fork 9 (.fork 4 (.leaf [(0,32,413,2,9),(4,0,443,0,9),(8,0,439,0,9),(16,0,431,0,9)]) (.fork 2 (.leaf [(32,0,415,0,9),(0,4,187,256,8)]) (.leaf [(0,16,430,1,8),(2,32,413,0,8),(0,8,311,128,7)]))) (.fork 5 (.fork 2 (.leaf [(1,0,430,0,7),(256,0,187,0,7)]) (.leaf [(1,16,430,0,7),(256,4,187,0,7),(128,0,311,0,6)])) (.fork 2 (.leaf [(128,8,311,0,6),(5,16,426,0,5)]) (.leaf [(9,16,422,0,5),(264,4,179,0,5),(272,4,171,0,5)]))))
def levels447 : Nat → Packing
  | 6 => layer447r6
  | 7 => layer447r7
  | 8 => layer447r8
  | 9 => layer447r9
  | 10 => layer447r10
  | _ => emptyPacking
def index447 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 16 0 6 2 0 keys447k7
  | 8 => lookupWord 5 31 2 9 5 0 keys447k8
  | 9 => lookupWord 13 53 5 10 6 0 keys447k9
  | 10 => lookupWord 4 37 2 8 4 0 keys447k10
  | _ => fun _ => none
def g447 : Forest := ⟨447,10,fun j => samples447[j]?.getD (0,0),cols447,#[[]],levels447,index447,noFactory,noFactorySound 447⟩
def packed503r11 (i : Nat) : Nat := 0x1ff
def layer503r11 : Packing := (1,0,0,63,0,0,1,packed503r11)
def samples503 : Array (Bits × Bits) := #[(0x204800061872001fff88c24d5b267000fff0f303f300033cc003ffff,0x2d20482a8208120b482d8040440902305a05b07301730aa11cc2c950b3),(0x1100006700018665c001800110c72a4db9fff000303f33c000ccfffff3000,0x1141b06721988265c86da1b000450004a9437436101733c466445519f346a),(0x92200000000063879fffe00066318338e3e000000c3c3c3fffff0f0003c000,0x922087000043a2829611e04722108338e3e10e10e414141510ff0f045bc11a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffae3c000c780007c07e0000000783e03c0fc0000000fc03fc0000ff00003ffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffae3cd92c786d17c07e1b486d2783e03c0fc0f24f24f803e80f44ee03d12af4c),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcfc0000f800007ff8000000007fc003ff000000000fffc000000ffffffc0000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcfc09a4f804e277d8013904e47fc003ff000b48b48efe8000b88bbaae600b90),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000ffffff8000000000007ffffc00000000000ffffffffff00000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0001386ad8bc0000002e00b85def7c00000270270bebebea2f00000b8002e0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000007ffffffffffffffff000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb661c00000c00000003000c07fbbabf6b5438038000000003000000c000300),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000000000000,0x499e009527005d7569c0170000000000000c00c000000000c0000030000c00)]
def cols503 : IndexTree ColumnInfo := (.leaf [(16,0,487,0,11)])
def levels503 : Nat → Packing
  | 11 => layer503r11
  | _ => emptyPacking
def index503 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g503 : Forest := ⟨503,11,fun j => samples503[j]?.getD (0,0),cols503,#[[]],levels503,index503,noFactory,noFactorySound 503⟩
def packed495r11 (i : Nat) : Nat := 0x1ff
def layer495r11 : Packing := (1,0,0,63,0,0,1,packed495r11)
def samples495 : Array (Bits × Bits) := #[(0x92490021c393e400fff83a1391ba50027003ffcccccccc00cccc00,0xf924906e0c191641e41f81a11909a507a30781fcccccccc36cccc3a),(0x2400038e00060ce33800c0004c1c024c60039ffc000f0ff0f000ffffff,0x2505038e424204e3390ad0a00c14000c642a942d0a0505f0f112555513),(0x108000000003870fc3fff00018060e38f8003e00000f0f0fffffff0f000,0x10823000008e850b42c2702608020e38f811be118465050555447f0f04a),(0x23000e3f0003f80ffc000000e0f80fc0ffffc000000ff00ff0000ff0000,0x2330fe3f0c6ff80ffc31e31ea0e80b40efc7c0c7b1eff00ff0336ff033a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbc000fc00003fff000000000ff000fff00000000000ffff000000ffffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbc26afc009cbdfb000274274ff000fff00b500b52d4fafa0002e4aaaaec),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000ffffffc000000000000fffff00000000000000ffffffffff000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc004cb6db170000000058058f7fdf00000260026098afafaaa8b80000b0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000fffffffffffffffffff0000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd487000001800000000600605e16a4b6103814380e000000000c00000c0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000,0x2b7804924e0172e4a9380b800000000000c000c03000000000300000300)]
def cols495 : IndexTree ColumnInfo := (.leaf [(8,0,487,0,11)])
def levels495 : Nat → Packing
  | 11 => layer495r11
  | _ => emptyPacking
def index495 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g495 : Forest := ⟨495,11,fun j => samples495[j]?.getD (0,0),cols495,#[[]],levels495,index495,noFactory,noFactorySound 495⟩
def packed479r11 (i : Nat) : Nat := 0x1ff
def layer479r11 : Packing := (1,0,0,63,0,0,1,packed479r11)
def samples479 : Array (Bits × Bits) := #[(0x9240018727c803ff80d09804d28027007fc3c3f333007fffff,0x5009241200122c82905805088005282a30502c1417333092aaa13),(0x49200cce3801965c67003004360e49b630039ff8033333c3c00666600,0x4930fcce3a37965c6747b8f4160a4896347a98fc7b3333c3c9b66673a),(0x104000000001e79f87ffc000c03071c7c003e00003c3c3ffffff87800,0x104230000046a2968589c130401071c7c11be23119414155523f8784a),(0x61800f0fc001f81ff800000707c07e07fffc000003fc03fc0007f8000,0x6190ff0fc237f81ff84788f507405a077c7c08f47bfc03fc09b7f813a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7e000ff00001ffe000000007f8007ff80000000003fffc000007fffff,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7e16aff002e5ffe0005d0ba7f8007ff807500ea753ebe8000f25555ec),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000ffffffe000000000007ffff80000000000003fffffffff800000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8004c55b6cb80000001602c7bfef8000026004c262bebeaaa5c0000b0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000007fffffffffffffffffc000000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9247000000c0000000180302e8b5256883814703800000000600000c0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000000,0x6db80aa493015d6952602c00000000000400080400000000080000100)]
def cols479 : IndexTree ColumnInfo := (.leaf [(2,0,477,0,11)])
def levels479 : Nat → Packing
  | 11 => layer479r11
  | _ => emptyPacking
def index479 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g479 : Forest := ⟨479,11,fun j => samples479[j]?.getD (0,0),cols479,#[[]],levels479,index479,noFactory,noFactorySound 479⟩
def packed511r6 (i : Nat) : Nat := 0x30d1a2759d2329b025d8460f20a9d6748ca6d18764087
def layer511r6 : Packing := (2,7,5,63,0,3,1,packed511r6)
def keys511k7 (i : Nat) : Nat := 0x500
def packed511r7 (i : Nat) : Nat := 0x2567a28a567a28955820000000006981c4c0f8c6cdf8be089e31b3fe2f82200001040000000000000000aac1000000000000000000000000000000dd67b1b87c0deeeb6fb4d628f1571b75aed165b157eb959ab54ea14da551e893c1c8d86630168a84e241087836180a8481e0c04818060071a6758ca6c09761183e3c4e9194d812ec23078798ca721b025d8460e479ba56636cd412e9848b775acc6c9a825d30a1e6e9554dc12ec326147c5d2aa9b125d864c285bbad553704bb049851b575aaa6c49760930c966e3384dc12eb126172c5d125d86609624c27593a46434cc32e0984eb2758c8689825c130a0dcecd5458348c390f21badd329b461d9021f03757665368c3b2043e82e758ca6d18764087d0d4e9194da30ec810f11b9dc260b0691875da9171b6e230ed010f335436758ca6c09761d83a8e4e9194d812ec3b0781daccaa9b025d8760ea1b3ac643604bb0ec1d472748c86c09761d838accee12e58348c3b0730dadd7009761e6660f21b576e012ec3cccc1e0e6329c86c0976118398cd6eb804bb0ec2307919abb7009761d8460ee133a04bb0f33308c1c46e770982c1a461d72a4d46db88c3b4043c4529cadd700a761d8388b139576e014ec3b07115a32740a761e6660e22b4c4e814ec3b08c1c4550d9d6329b825d704c2a393a4653704bae0986076b32aa6e0975c130c0ece5b505412eb826190d9b8718a825d704c3239370e11504bae0984c36b75c825e665c130d06d553904bcccb826131cadd72097889704c3439554e412f112e0985c327609799a225c130
def layer511r7 : Packing := (49,6,5,63,0,9,1,packed511r7)
def keys511k8 (i : Nat) : Nat := 0x241d390467fc69869276766709ab17800057b00026c2a969000cd1a2eee50087800055f1dd461a4bedce0000f3c0b3295bd2464002256302700000000008b553161c3b58e3c8847c42850030050010462411c8c00002
def packed511r8 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xd2d6886c4979998396dacc6c09799983d2da886c09799983d0debb25d8799983b0ddc025d8799983ba98c06d18799983b4d9c025d8799983d396886c49761183979acc6c09761183c798ca6c09761183d399c86c09761183d39a886c09761183d19ebb25d8761183b599c025d8761183b695c125e6661183b699c025e6661183f09c9761e6661183a9d9c029d8760d8291facc6c09861d72c1faaa6c09861d72d1d9c36c09861d72b1b9c0261a461d72d1b8982c1a461d72b1b9c0261875d172a1decc2a58760d72c1debb2a58760d72a1ddc02a58760d72b998c06d18760d72e0dca961e6660d72b0edc62627760972b2adc62617460972a9d9c029d8760d6289edcaaed8721e22b9a8c06d18721e22a9eacc61da021e22c9eabb61da021e22e9a9c461da021e22d8e9876c08799a22cbc6886c4a760e228fcacc6c0a760e22cbca886c0a760e22c9cebb29d8760e22a9cdc029d8760e22bb88c06d18760e22adc9c029d8760e22c9ccba61d7660e22aec5c129e6660e22aec9c029e6660e22e8cca761e6660e22af85c129d8460e22af89c029d8460e22e98ca761d8460e22a1decc2a58760d70c1debb2a58760d70e0dca961e6660d70d1ccb961d8388970d1d8b961da360170d1d8b961d8360170b0edc22627761960a9d9c029d8760d6091facc6dc9860160c1faaa6dc9860160b1d9c7261a360160a9d9c02a1875d930aacdc22a1865d93092decc6e09799930d2d6886c49799930a9d9c02a1875c930aacdc62a1825c93093cecc6e09788930d3c6886c49788930b2cdc825e6688930b6c5c125e6688930c5d9cbaa8975c13095d9cbaa8975c130d1dacc6e0975c130d1d8ca6e0975c130d1daaa6e0975c130d1d9c66e0975c130d1d9c26e0975c13095dacc6e0975c130c5daaa6e0975c130d1d9b86a0975c13095d9cb2a0975c130d1d9b82a0975c130e1d9a82a0975c130b4d9c62a0975c130b5c9c22a0975c130e1daaaa20975c130d1d9b8a20975c130b1d9c825da65c130b1d9c825d865c130e4daaa25e665c130b4d9c825e665c130f0da8825e665c130b1d9c825da25c130b1d9c825d825c130b1d9c825d625c130e5caaa25e225c130b5c9c825e225c130f1ca8825e225c130f4c89799a225c130a9d9c029d8760d20b0edc6262776092091facc6dc9860120c1faaa6dc9860120b1d9c7261a36012089f9caaed8721e00aae9c22a1865da00cbd2886c4a760e00c9dabb29d8760e00c9d8ba61d7660e00aed1c129e6660e00e8d8a761e6660e00c9d8ba61d835ca00aae9c62a1825ca009fc1c12dd8388a00d9c8b761d8388a00a1b8ca6d1876408791dacc6c09761d83c1daaa6c09761d83b0d9c025d8799983b199c025d8761183a9c9c029d8760e2291dacc6e0975c130c1daaa6e0975c130b0d9c825e665c130b1c9c825e225c130 else 0xa7d8c968da260170e9d98768da260170a5ddc3aeda726160a5ddc7261a39dd60a7cdc2261a39dd608fd9c02e9835c9609fd1c12dda360160a3ddc6aeda825d30a3ddc2aeda825d30a3decc6d9a825d30e3ccc26d9a825d30a3decc6c9a825d30e2dcc66c9a825d30c3ddb66c9a825d30c3dda86da8825d30c3dda86ca8825d30a7d5c6a21a125d30a7d5c2a21a125d30a7cdc2aa89761930c3deaa6e09761930c7d6aa6c4976193097cdcb25ca261930b3cdc825ca261930b7c5c125ca261930a6ddc6aa89760930c3deaa6e09760930c7d6aa6c4976093096ddcb25ca660930b2ddc825ca660930b6d5c125ca660930b3d5c125d86609308fd9c02e976609308fd9c02e9865c930c3ddca6e09758930d2ddc66e09758930d3cdc26e09758930c3ddb86a09758930c7d5a86c49758930b2ddc825d8658930b6d5c125d8658930b3cdc825d8258930b7c5c125d8258930f2cc9761982589309dd9c72e2aa5c1309dd9c7aeda85c130dec9b66c8a85c130ded1b66c4a85c130dfc1b26c4a85c130b9d9c8aa9875c130bcd9c62a1875c130bdc9c22a1875c1309dd9c7aeda65c1309fc9c22e1a65c1309dd8cb61da65c1309fc9c2aed865c1309ed8cb699865c130bad8c8699865c1309dd9c7aeda25c1309ed9c62e1a25c1309dd8cb61da25c1309ed9c6aed825c1309fc8cb689825c130bbc8c8689825c1309bd8c86e9625c130fac986609625c130a5ddc3aeda726120a5ddc7261a39dd20a6ddc6261a39dd208fd9c02e97660d209fd1c12dda3601209fd1c12dd8358120a1bdc9aa9a461c87c9baaa2c1a461c87b4b8c06d18765887b5a8c06d18764887c1fabbaa98764087e1b9c4aa98764087d1babb6d18764087b1b8ca6d18764087e1baaa6d18764087a5b8ca6d1876408791facc6c09861d76c1faaa6c09861d76d1d9c36c09861d76b1b9c0261a461d76d1b8982c1a461d76b0edc2262776197688fdcaaed8721e66b8b8c06d18721e66a8facc61da021e66c8fabb61da021e66e8b9c461da021e6689bdcaaed8721d84a9bacc61da021d84c9babb61da021d84e1b8b961da021d84a9b9c02a1875d974aaadc22a1865d974c799c4aeda025d83c3d9b82e1a025d83a6d9c62e1a025d83a7c9c22e1a025d83c3dabba21a025d83c1ddcbaa89761d8391ddcbaa89761d83d1dacc6c09761d83d1d8ca6c09761d83d1daaa6c09761d83d1d9c66c09761d83d1d9c26c09761d8391decc6c09761d83c1deaa6c09761d83b1d9c025da661d83cb9aaa2c1a461d83b1d9c025da261d83b1d9c025da061d8395dacc6c09761d83c5daaa6c09761d83d1d9c86c09761d83d1d8c86c09761d83d1da886c09761d83b599c025da461d83d598972c1a461d83b1d9c025d8761983a1decc2a5875d983c1debb2a5875d983a1ddc02a5875d983b998c06d1875d983) else (if i < 3 then 0xc4101b9ecc141c6020400000000000000000000000018a5c5f063b27c5f445f17d117c5f445d27d117c5f445f47c51719f445c67c5f447c67c5f4472d69634b025752b49574a7a53127e932497a49d23e917487a3f51e08e346b23391828b9451225511a88a44121ad0bc851424a0f105e81840820350007fd3f59f8cfc07ce3db9ebcf4e79f3c41decedc7663af1d44e9273c3979c88e2a70837d9be0dea6f23729b38d8c6be35d9ae0d6a6b23551a88d346923451a08cfe67c33c99d8ce666b3341994cc465f32e1950ca264e325990cc7663831a98b4c4a61d30a9820c005f82f31750b845ba2d69680b305862ba159caaa53e29b1490a24505279937098a4b325812b495449d24311f88f647823811a08ca46222f914889e447222110487c43b21c10d486442f21610a484c423210107482040d20510087f43e31e60f2478c3c31e00eb87563a31cd8e6072a3881c00dcc6cc3631b00d6068c3431a00cf466a3321978cb06163081828c085fe2fc17a0bc45d22e11650aa454229e14d8a4c51628814009f44f427713a09c44dc26b1340994492246121890047023511908bc458229113088c44021d10d085c41e20c10488184062000fc07c03da1ea0f107683a41ca0e387103821be0dd86e036a1b20d786b03521a60d1868033a19a0cb865030e1750b405802b01500a40500270126091848023a11a08904142040ff07b83d01ce0e406b83501980c9063030c1800bd05d02dc1680b105702ac1500a5051027c13809904b01fc0e406502c012c07c0310120048000e799c3a64a06518787ddc02ea8864e7787dcca6da8864e7787dcca6ca8864e7787dcca6c28864e77a7cdc2a65a39dd86adb8c0691a261d768f9ccba21a39dd84c7b8c96c0a85d974cdb9c76c0a85d974e799c4aeda025d83a7dacc6e1a025d83c7d9b66c9a025d83a6ddc62e1a025d83a7cdc22e1a025d83db9aaa2c1a461d83db99a62c1a461d83bb98c0691a261d839b9ccba21a461d83cf9aaa2c1a461d83db9a882c1a461d83c7d8ca6c09761983bb98c06d18761983d79acc6c09761183d799c86c09761183a6ddc6a65a39dd82c7d8c96c0a760d82bb98c06d18760d82abd5c129d8660d82abd9c029d8660d82cdb9a62c1a461d72c7b8ca6c0985d172d5b9c76c0985d172bb98c06d18760d62bacdc39dd866096287dccba65a39dd80c7d6996c4a764d80b1ddc7a658764d80a7d5c129d9664d80c7d6996c4a760d80b1ddc7a658760d8097d5c12dd93649809aedc22e19661970b9d9c0aed8760d70b8ddc62618760d70b9cdc22618760d709aedc62e19260970b8f9c62618760170b9e9c22618760170add9c7aa9a360170c7daaa2e5a360170d9d8cb61da360170e9daaa61da360170d9d8b961da360170c7d8b9699a360170e9d987699a360170d9d8b961d8360170 else 0x7c4080000068e08065b841328e10401c80dcc0fc40fc40b22e57821bcde085b3f8210c5e084e502c8f8213220e37d3783d388c8b481345080c8838d78fd0f8c2635a3058d68c138c0956d104ca3441635e9f8dd089830203c9f00406cdb17c01b88081d3f45f007e634df17c321540e280e280f98d3fc5f0c98a6c81629b2047202f203f171813c80dc8b085735c415cd7105722c216cfb105b3ec4100001d37841719e3fc5f0087102710300100073433103310271027103a0c304000006830c10000019342000034d0b4f080064c0e4d0e4e0e4f0c4ce0c432023203c67c5e087c67c5e087c67c5e08665038a6c81629b2043203c67c5e0c6327c5e087c67021719f17821f19b37c5e0c83203c67c5e0c6327c5e087c67021719f17821f19b3fc5e0c9c66cdf1782271833702180001e37841719e37c5f009e3030418a038a020010628558406280800010400010000400000468e104001f003360268fc7f162121a3f1fc588480000000cbc0764603ce0bcc08006cfb304f003b3ecc12d9b105040f1020cbc8f046041074c0800018d795e0f4ff41d6301001001e08303c00bc10fc0567452cc8cdb35f1fc1d155933c00c006c00ec10c1e38200004100000007438d78df41d6280001e30204000100004004007420c0001041e003e043001080248022803f102000000000001000001001000001c63c41032f23c11bc9f104f382f303c603c603714208420cdc970470410017103b3ec41010718081b36))
def layer511r8 : Packing := (313,5,5,63,0,13,1,packed511r8)
def keys511k9 (i : Nat) : Nat := 0x24bab50005a36e588bc1806904000e06e7a032609e0fa581929fe0cc01d3dba9aa6e24b40b64c8c2307075001e558e4adc79931ae2e82300af88adfe00030610ec0000000000002c1649d000000226107c276b40a1d606a973e992908c74000721d9fb210071c893654427f8868980000510001910001017f06a46a1360f1000000213e02c83b7ba7a5600098f291800000044193c359725fc56334e478218923a18d8d3c59a6600000b98d893f3350890c6fe7b62a5defed7235a36d86bedd1908012da2ec267c845be5165e97978018aa05df5f5aadc70c21333893489525374c82165bc09617e687416901ca680c4cd136e694ae47684b6b766e4c6e26d0330520959a2a929266dcd06308bd64871c5dc2007430138acdaea3f1b7289c3261e367124b573062032d37e806b118444a2acea43ee22c320d9ee2b0005a79ca573342061e0001b2331781f6d55ca14901c28a3ed190000868e2400004c00008b1c05e1ef932262000b7f79e800000039392ef18a0000005838000000847b9cbc6448077670c7219f35797f86c21c4ef741000160b70b00024bb228308f39e99b9828eec150abb902b0d07ac24e88710f44e5be24b700925c44b4a44d24a5d1425cc2e4e958336a0d96507656b96c69d26f820abcc1e48630132fda03697658a41e46ff1ca6258e85ade08b6ccac80efe2d960023305d013d4a2a4702925725b3b0c5d00ea000422c425ee051029bae70cfb0000001c7281f86af1a0001054e140001d1c2a800038fe0b480aa182390000c7f00070a614aed2a59ba6a4922428c5411b2008413000c3860c0888b0200a06080198010e118b049c005023001024242131810103004405970140802611e832e2821c5a90009363c0263a0024500002a518087810600801041410000706b0281028718500800020185
def packed511r9 (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0x25e224c39e74412f11261e73a2277889309f9974c34449876ce9999a224c3b66cc4cd11261eb3a226688930ed992f33444987cce7799a224c35ecd4150b82617b66d8a85c130bf9364542e0986bdaaaa21704c39ec5cd10b8261d76aa8975c130ebb3504bae09875d8a825d704c3aed4412eb8261776aed875c130dbb554c3ae09875d8b961d704c3cec5430eb8261e76a21875c130ebb12ed32e09875d897619704c376d554ccb8261eb6a22665c130f9b30f332e09875d897689704c3aec4bb04b8261d7625d625c130df9555112e0987bca88889704c3ee4c3c44b8261fb299a225c1308bfd76d39309054fdb6262774827ead894ec1a413f66c0a760d20d3b94ec3b069071ec989dd824831fd55130c02414fe6dc9860120a7f172c3b009071f8989dd804839ec4c346c0241a7e69ca7a2200b3f576c390f004efabb6988780357d4434c43c01b3e61da621e00d7b510d190f004feabb688878035f54434443c01b7a61da221e00d7e510d090f0079da8868e778035ed443473bc013fa6caaa61a009fd364542ed0069f8a861d7680357c5430cbb401e3e61c8799a00bdb36643ccd005ee9b221e66802f78d890f33401e3ea227799a00f9b3673bccd005ed9b39de66802decdbd10c1c01af6a20a760e00b7b576c3b07006dd8a761d83803ced444eec1c013f62e97660e00f3b30ebb307006edaaa99983803d6d444ccc1c01bb629e6660e00f5b30f33307007cda779998380277cdb554c14013be2ea6660a009df36c542e50069f8a861d728027ec5d306b9401e7661d835ca00d7d150c12e5007ae98660962803cf4c390f114017ba6d88788a00bf936643c45005fe1b121e22803cf5444ef11401f726ce7788a00bf93673bc45004fe8ba61a22803d75444cd11401f3a9de6688a00bf9576c1c45007bca8860e22802fe45bb0711401ef261d8388a00fb94eec1c45007eca6660e228020fedcd54c390f66e2c1a461c87a3f576c3b2043e1faaa61d9021f8dcda30ec810f47e6c09861d76a5db644c30cbb68f9876808799b4dcc3b4043b098f5a21a125d838fb576d012ec1e3da886809760f0ef5512ec3b074776c09761d83b73160d230ec1d5d9b025d8760f0ee54b0ebb3075b56c49799983adb3604bcccc1f0dc9761e6660ebcad892ec23075e66c09761183e3392ec3b08c1d1f9b0261875cb0ee54b0ec1ae54bb6d89860972d3d30ed010f114fc5b129d8388a7e4d814ec1c45a7329d8760e22c3b952c3b06b852edb2261865828fcdb930c02c10f7aeda825d30c7ad10d092e9852ddb825e664c2b6ad892f332614f36e09788930af8b624bc449865daaa25d704c2aecdc12eb8261c76a20975c130e9b12f332e09875c897889704c2976db130c124147e6dc98601209fa36253b070069d8a761d838028ecd812ec3b074766e0975c130 else 0xe5c6f261a461d72bb7160d230eb953f9b0261875caa7edb1313bae557e6c0989dd72ad7b6c4c2e8b957b9b0261745cb8de4c30eba2e51f7aeca960d728fbb6054b06b959debb61d835cbcceda30ec1ae59b72a66660d72f1bb0f33306b971ec989dd825cb9d64c2e8c12e53f56c4a760d629fb36053b06b169dca761d8358bc773bb0cc12c5eab6197460962bf5160d230f1159eebb61c8788bcd6da30e43c453faaeda021e22d3db0ed010f1179ce8868e7788b5e7443473bc4597b2a67761a22f1db0e43ccd115ecdb321e6688af72d890f334457ba6c08799a22f1dd113bccd117ccdb39de6688af66d9cef33445b6b2ea7761222f35d113bb09117d8db39dd8488a7d65d4eec24457e36ce7761222f55d1133309117cae779998488b5d65d510ba4453eb2ea885d222f35d113bae91157acb96197488bd57444ccba445f2b9de665d2229f9b6155307116bce8829d8388a7e6d814ec1c456f3aed8760e22f71b68c3b07116dcca761d8388bce7444eec1c453f32e97660e22f39b0ebb307116eceaa9998388bd67444ccc1c45bb329e6660e22f59b0f33307117cce779998388b7c755308c1c45be329d8460e22f71b0ec2307117d8e776118388bf4733308c1c45ee3a217460e22fd1cccba3071158fdb625d87602cf6d912ec3b01a3f61da621d80d3db0ed110ec061fca961d766027ead894ec9b0197729d9764d80d3b94ec3b26c04fd9b0aa9836027ead894ec1b01a7729d8760d80c3f952c3ae4c061feaa261875c2a7edb1313bae157b6c8989dd708fbd7654b06b863dca9a21835c2cef5db0ec1ae1a772a58760d70e3bd32c3b06b865dca961d835c336e54cccc1ae1e3761e6660d70af9972c1c44b879cd8760e225c31fd55130c02e167eaed8760170d3f554c3b00b871f8a961d805c38fd4cb0ec02e1c7e2627760170f1f30f33300b857d8b968d805c39ec4c346c02e17762dda360170f3b30ed1b00b857d8b960d805c3cecc3b06c02e1e7a61e22601708bfd76d3930b055edb22627758387e4c4eec32c13f56c4a760d609fb36053b06b069dca761d835831fd55130c02c14fe6dc9860160a7f172c3b00b071f8989dd805839ec4c346c02c18f7aeda825d30c7bb6cd412e9863ddb26a0974c23ef5db504ba618f76a28825d30cfad10d092e9871dcb9a22774c27e6d9554c32614f76e09761930afab624bb0c984fcdb22a1764c27ecd8150bb261a772a1875d930d5b950c32ec9872dcb9a22664c396f4cd1133261cb76628899930adbb704bccc9872de8825e664c3c6f444ef332613b76daaa60930a7bb704bb049857d5b125d824c276e5d4ccc12613b76d8a85c9309fb360542e49869dca861d724c35e654304b92614f76e09758930afab624bac4987acd86609624c39e65cd1111261cf3a668888930e79b31444449857cdb8) else (if i < 3 then 0x7654aec9047fdb82a576482bef5d952c1a41cf72e58760d209fb974bb3069057dcb95d983483ceec3aecc1a413fb2ea7760920afd9733bb04905fcdb39dd82482f7cdb14ec02417f66cca760120bfe36253b009057f8b99dd80482fecd9ceec0241e7e61d7660120bfb16ed1b00906fd9a768d80483decc3b46c0241bf6699a360120bfb3673bac0905fd8b760d60483decc3b06b02419eea64a065187d7751050328c3e7b9962819461ebdc58328c930f87f6e6aa61c87a3fb735530e43e9beaa6918721e2fedcd54c390f76e2c1a461c87a9fd76c3b2c43f4bdb461d9621eaf75db0ec910fd6b6d18764887cf73695532043e3faaaa219021f8fd5db0ec810fc7e2e98764087e3f554c3b2043d5fabb61d9021f2fd5530ec810fd6e6d18764087a3fd76c3b2043e1feaa61d9021f8fcd830ec810fa772ea8864e779bb975443273bddb8b0691879df1ee5d510c9cef1f72ea8864e77abdb654cceec347fabb680985db3ecd9b404c2ed87faa89861d76a3fb604c30ebb71bc98691875daedc58348c3aed4fe6c09861d76abdb644c4eebb55f9b0262775db87e4c4eec32ed7ae2c1a461e66b1fd76c390f3378bdb461c8799a77d5db4043ccda3f61da021e66f1bd10d1cef336ade8868e7799acdf5db0e43b093eeaeda021d84cf7172d010ec271bca9a2277613ccf443473bb098ef2a6889dd84cb7952c3ceec26b9e8868e77613a5e5ccef33309e2fa227799984f93b673bcccc256bcb99de66612f4ed9cef333098ef2a5a7a2174a77972d3510ba53bcb968a885d23de5cb4d442e91ef2e5a2a2174a779734430eba71bcb9a22775d2ade5cd113bae93eb6caaa619749f5b64542ecba4fb9b02a1765d34de5430ebb2e9aaf2a1865d974e57973444ccba56bcb9a22665d3c5f444ef332e99f5a21a125d83cfb576d012ec1e7d9b86809760f3ec5c3404bb079f6a21a025d83cfb36cd012ec1e7d9b26809760e3ef5db404bb078f7a21a025d83d3bb6f5530ec1f1deaa25d8760f8ee4bb4cc3b07ae7aa9a461d83e3b92ed130ec1f1dc976818760f2ef5512ec3b07c77a209761d83abbb604bb0ec1f59c976918760efcc58348c3b075f56c49761983afb3604bb0cc1f1dc9761d8660e3ef5d952bb3071f76c0a95d983b3bd76c3aecc1f99db461d7660eb6ed853333307cb7a209799983adbb604bcccc1dadebb61e6660fd4eda30f33307d3725d8799983f1bd113bcccc1f39e8825d8460edcf5db0ec2307d6725d8761183f33d113bb08c1f69e999998460fb4e4bcccc2307ea761e6661183f93cef33308c1eb9cbaa217460e7ce5d510ba307ea7a22665d183a9fb6d4cceec164fca99de6660ab5edb532ba3055af2e6665d1829fab6253b06c14fd9b029d8360b4ee53b0ec1b051feaeda026172cfb366d0130b961feaa261875ca8fed8130c3a else (if i < 4 then 0x5c2f7cdb130c02e17fa6c89860170f3f576c3b00b879faaa61d805c3cfc54b0ec02e1e7ea658760170f3f36cc3b00b879f9b261d805c3cfc4c30ec02e1e7ea218760170f3f30ed3300b84ff8ba659805c3cfcc3b2cc02e1e7e61d8660170f3f30ebb300b86fdaaa68d805c2fec5cb46c02e1f7661da360170dfb34cd1b00b85fd8b960d805c3eecc3b06c02e1e7e61da260170dfb346d1300b84ff8ba649805c3cfcc3b24c02e1e7e61d8260170f3f30eb9300b879f987589805c32ff5db4e4c2c11ffaeda7261608ff9735530eb047febb2a5875823fedc1533bac11ff2e9989dd60abfb6e4c4eeb057edb2262775833ef4cb473bac19f7661a39dd60cfb930d1ceeb04efcba9dd86582b7e5cceec32c17b76ce7761960afbd7654b06b073dcb961d835823ff5d952c12c11ff6dca960960cfbb6654b04b047febb2a5725823fedc152b92c13f72e9835c960cfb952c1ae4b079dd8760d72582fecd994ec02c17fa6c8a760160bfe36253b00b057f8b99dd80582fecd9ceec02c17f62dda360160dfb34ed1b00b07bd98768d805837ecd1b44c02c1e7e61d7260160cfbd76d412e9867ddb66a0974c33eed93504ba619f76a28825d30afbb6d4412e9857ddb2a20974c33ef55152c3a619f72a5a661d30cfb952d130e984fddb7aa9864c33ef5512ec32615f76e09761930ef992e5130c9875dcb961d764c27eedbd54c12619f7aa89760930afbb704bb049876dc97299824c39ee4bb0cc1261cf766186609309fb974bb3049875dcb961d724c27ee5d30cb92615f76e09758930cfbb504bac49876dc97619624c3be64bb04b12617f66e2aa5c130bfb171552e0985fd9b6aa9704c2fecd9554b82617f6aeda85c130bfb576542e0985fd9b62a1704c3f6cdb150b82617f66c8a85c130ff9364542e0987fd1b12a1704c2fecdd510b82617f62ea885c130efb173442e0985fd9b6a21704c2fecd9510b8261f76aed875c130fbb554c3ae0987dd8a861d704c3eed4430eb8261f766d9875c130fbb364c3ae0985fdabb699704c2fec5c34cb8261bf66a1a65c130fbb30ed32e0985fdabb619704c2fecdd30cb82617f62e9865c130fbb30ec32e0987ed9a6619704c3fe45930cb82617f6aeda25c130bfb170d12e0986fd9a8689704c3eecc3b44b8261bf6699a25c130bfb576c12e0985fd9ba609704c2fec5d304b8261f7661d825c130fdb16cc12e0987bd986609704c3fe4d1304b82617f66e9625c130bfb370b12e0987dd987589704c3f6cc32c4b8261ff2609625c130cbfd76d39309047febb69c984823fe5cd54c3a411ffaeca961d208ffb7054cee9047fcba66277482afedb9313ba415bf6d8989dd20cfbd32d1cee9067dd9868e774833ee4c3473ba411ff2ea7765920afbb673bb2c9047febb2a5864823fedb952c32419f76cca9619208ffd else 0x76ce77619629f79753bb08b15f9db39dd8458a7eed814ec1ac5ee76d18760d62bf9b673bb04b17aee776198258b2fed394f4cb012ff6e2aa65d80cdfd32d312ec067de9968c976033f74cb444bb019fda65a125d80b7f3615530ec059fdb7a65876027fcd8554c3b0157f6de9961d808ffb754c90ec066fe99698876033ef4cb4643b019fba65a221d80cfed32d090ec067de9968e77602beed992ecb3015fb6c89765980afeb624bb2cc047febb2a5766033eed9952bb3011ff2ea995d980afbb6f4cb26c067de9929d93602bef5db2ec9b01af72e98764d80e7bd32c3b26c067dca7659936039eec3b2cc9b013f72e97664d80afb972bb326c079dd875d993602beedbd32c1b019f7a64a760d80e7bd32c3b06c056fdb625d92602beed992ec93015fd6c49764980afb96ec9b24c073dd8764d926023ff5d952b93019f76cca95c9808ff9754cae4c04fdcba64d726033ee54b26b9301e7761d935c980cfbb66d4532b863fda82a2995c33eed43474cae19f72a1a3a6570cfbb4cd1d32b867dda368a995c26fedb9514cae13fe6c0a8a65708ffb6f55330b867ddb3aa9985c2afedbd54cc2e15fe6c2aa661709bfb6f55330b853fdb8a65985c337f4cb4c4c2e19bf661a626170ddbb4cd1930b867ee99688985c33f6cc3444c2e1bbb699a226170df9b46d1130b86ef5a6684985c37ead1b424c2e1bf9689a126170ddf34cd0130b86fe9a2680985c23ff5d953442e11ff6e0a9a21708ff9754cd10b847fcba662885c23fe5cb4d442e11ff2e5a2a2170bbf3615530eb859fdb8a65875c2e7edb130c3ae177b6c89861d709ff3615530eb853fdb8a65875c26fedbd54cb2e13fb6c8a8659709bf974c3b2cb847fdb9aa9865c27f6d9554c32e11ffaeca961970cdfb6c54b0cb847fcbaa65865c277e5d32cc32e16bf2e19661970cfd9525130cb84ff9b0aa9765c27f6d9150bb2e19f7aeca960d70cfbb6c54b06b867ddb22a5835c2beedc532c1ae19f72a69960d70afbd76cc306b867dca9661835c2f6edb130c1ae17f36c89860d70afb97344306b867dca9a21835c3cef5db0ec1ae1e77a658760d70f3bb6cc3b06b879ddb261d835c36ee54b0ec1ae1e772618760d70f3bd10c3b06b84fdcba659835c33ee54b2cc1ae1e7761d9660d70afb972c3306b867dca9619835c3ceec3b0cc1ae137f6deaa649709dfb6c54324b84dfcba61d925c27ee5d306c92e15f72e58364970f3bb0ec1b24b847fdb9aa9825c277edb554c12e11ffaeca960970cfdb6454b04b847fcbaa65825c337e5494cc12e15f72e58360970cfb952c1b04b879dd8760d825c27f65d324c12e16fb2e192609709ff361552e4b84efdb62a1725c25fe5c352b12e11ff2e5a858970afb972c1ac4b879dd8760d625c3d76c3304b12e177e6deaa60170cff55454b00b85bf9b8a658))) else (if i < 8 then (if i < 6 then 0xab235046948d1a19f233606648cb1193231e06300c48187230a86090bfa17c42f4c5dd8bac17282df05b20b55168c2be055e0aad154e2a845400a7114d6299452f8a5914a6293451f0a38146428b050e8a171422282c4fe09ed13ce27844ed89d5139e27244e189bd136e26c44d589a5132c26404c0897212d825984ab8948128424cc496891e1230242447d08f411a6233446388c1117622d445788a91146227444b8891111621f0436886710c2210040b07f50fa81ea83bb87440e341b7835a06930ce4194431c85fd0b9416802bb05550a6813bc255048908ac10b01fc83cf074a0e101b18342061e0b4c154827604aa08ac10501e0037e06300b58141022e0390054007e00ba00cc00067dda668e9961f3eed1b454cb0f9f76cda0a6587cfbb46d0532c3eddda768e9961fbced9d32ca30fbeea64a065187df751050328c3efb9962819461efdc58328c930fdee6d2aa640878ffd76d01313bc7fdb02a6889de3fe5cb4d444ef1ff2e5a2a22778ff972d05113be7dcbaa21939debeedb510c9cef5f76ca8864e77afbb61443273bdfb8b06918761a3fed81533bb0d5fb6ca999dd86cfbd32d1ceec357edb025c9261abf65ccee4930d7f36ce7724986cfbb66d0532bb67fabb680985db3fcdbb404c2ed1ffaeda0261768ffb6ed0130bb67ddb3680985db6ded2344c3aed7ee2c1a461d76df3b675530ec26fbabb680876133dedb1533bb099ef6c8a99dd849f7975444eec267bca9a22776137cf443473bb093ef2ea7761984af79733bb0cc25f9db39dd86612bde5cd10c3ae93ef6deaa61974cfbd76d012ec1e7ddb86809760f3ee5c3404bb079f7a21a025d83cfbb6cd012ec1e7ddb26809760fceedbd54c3b076f76c2aa61d83f73d54d230ec1fb9da66918760f5eed3344c3b07ee7691a261d83b7bd76d030ec1cfddb0aa98760f7cf55348c3b07ee7a21a461d83afbb604bb0cc1fb9db461d8660f3ef5d952bb3079f76c8a95d983cfbb6054aecc1f9debb61d7660fceed930ebb307e776c1875d983f73d76c3b08c1df9ebb61d8460efdc58348c3b051ff6c0a99dd82adfb6d4cceec167de9968e7760ab7ed812e4b3055bf2e67725982bdbb673b92cc15bddb39dd8660a3ff5d952bb3059ef6d0a95d9828ffb6054aecc14fbcba9dd8460abde5cceec23057e76ce7761182af7b6f4cae8c157bcb95d97460a7eed814ec1b05ee76d18760d82d7b94ec3306c17b9d865d18360b3eed9b414cae59feaeda026172cff36ed0130b947febb680985ca3fedbb404c2e59f76cda026172db7b4cd230eb95fb8b0691875ca3ff5d952c32e59ef6d0a9619728ffb6054b0cb957bcb9619745cb3ef5d952c1ae59f76d8a960d72cfbb6054b06b979debb61d835cbceedb30ec1ae5e776c18760d72bf7160d230eb147fcba6627758b3eecc3473bac57b else (if i < 7 then 0x2d145818ad3154629cc5188a1313ea26cc4af892f11da238446a88a510c6203c3f887c10eda1d3c39887130dc61a8433886410bda16642b485030982124421e83e9072a0d0417682ab04f6092c11681fd037606740ad8107018a02540328034ffe5ff9bfed7faaff19fd73f9f7efcfd75f99bf1b7de2fb1df60bea97d10f955f233e2e7c3ef7f9eeebdaa7aeef559e91bcf9799ef24de303c3f7818ef89ddc3b8e76feed79da33b1c75e4eb8dd613a9874cae8edd08b9e7737ae695cc2396c72a8e4f1c92390c71e8e395c66b8917116e1f1c32385e7056e071bfdb7ec6fccdf39bdb37b06f1eddb9ba6b72c6e3adc15b6936a86cfcd999b27362d6c18d7adae535a96b10d59daa7b5376a50d465a7c34e969a2d309a59b4926906d1ada29b4296822cf9d9e333b7673ece1d9b333456648cc0d971328b64d4c8dd90b31e36360c63d8b2b1446222c37985eb09360c0c0d980aaff45fa6be397adaf315e32bbbd7672ead5d06b9ad7252e055ba4b6a16b62d545a54b4256742cd0595eb21562dac435844b0055f02bc8574eae3d5bbab5f568eacbd58bab0855e0aad1549aa7b54d8a92d51e2a36543ca8614f2a9c4537ca6514c7297f52cea519492a90451eaa375462a89250d0a0f941328174ffe9f553c3a7784e8a9c4937d26eb4dca9b59363a6b84d529a69345a67c4cec995530825e64bae97212dca5a14b1295a12b125534a7694b1285a4fc49da92e925a24a5493e91b122a2445486c90c1210a41b482a903d1fba3f147d68f951eb239a47288e391bfa37046c28d6d1aaa34f46808cc5195a31c461a8b8d15ca2b3455a8a7913a2241441c882110121fc43da879d0cca14241fa82e1039a0373ff67fb0fee9fc53f7e7e9cfcc1f803ed07d88fae1f443e7c7bc0f511e663cae7920f0a9e063b947710edf1daf3b527668eca1d8e3afe75c0eb51d643abc7518e971d283a3273bce749cda39a872a8e4d9c4d38227008df99bc037746eacdd29b7236b46d2cd9e1b0935ac6b40d609a8e34fe6930d1e9a2e34506888cf319aa333665e8c9f192f3252648cc8e990531fe63e4c7998ed31ce6384c6d98d5319e6324c6198bd316e62a0c4c9893311a621cc3c187230c66174c2b9851309660f0c1b18273042606cc0617fd2fee5fc4bf117d32f9a5f1cbd797972f225e2cbc2977f2ee05d84ba917432e685bbcb7016d12d8459acb2e164d2c7c58bcb1016112bf257a8aed95cc2b685670ac695752acc555ca9f951e2a0c5394a6f94b528f251a8a2493f227c64e789ba136526ac4d4098592d825924b0c9511293251a4a1c925921823ca47588cd1155229e449487910b6210641408251044207c40e08191023202840387f20fb11eea3d987998f001df43bd07608e851c92390c71e8e371c5038647098e041bfc37e06f90de31bba37386cd8d681 else 0x98cf1061c4da6bcfe60a78bd18ca719086c35610a78bd18c9d16e4b025047043a0860087085be6f0733373f9861e2f466e5e3c30633c3e00c36081039dcd10f17a399339dcd10f4732573b9a21e8e64bcc86cf66f1243d1cc99cee68878a1be0e64e00ebc5ccf449a7d3143d1cc949ba7d378ca1cc9863a7f1f33292f9bc7e218e52582000003990d0610075e2e67a24d369ca1e8e64a4dd3e9bc650e64c2e0463a6f1f33292e9bc7e218e5258202869bd1ccd9ca50d3137c1ccd9cd2ef129f99e8934c00007321a0c200b8100001830818c87c78ce0f8b292f8f19c1f16525c64290c604e4f144e28432e4704610c638a38a031c8a0410c605e2e08743704702b3d8a2b3c38c8719818938940acd628acd0dcecd16321c660624e2502c660627043a08421c7e37085be0e666a8e3f1861e2f466a6e3430418cf0f8030d02040040000340400001a0200007001e042040000000000001041cc040e043c084001430a8610380081c0840e043c086013f004c1800000000000000000186130c2001e8f12523f0fa0d7949229e2f447e2f0fa238a7a3c2ac9035c7f0f8bd1293a1fe2f0fa251a78bc3e890361ae2787d0349a1be3f14424f1443d11fa3c5108fc5e88847e87645e7e0f98d794f44d91f3f9bc5e89429e2f469e426f8fc45093c450f447e2f41423cdf9ca04dcd3a3593f9b37e7d2668a1e89fd1ac28461be3787c5e89429e2f471a427c3bc5e1f44a34f1787d120b7c7e21849e2187a23f17a0611853d1cc8c9d0ff0f33d1286b19c7f1787d1378a21e8e6490df178e21cc94a1e8e6464df1943992143d1cc8c9be3287324c67a2211f9fcde2c67a25f478a211e33c5e848498cf17a121213e1de1e67a250de338de2f0fa2616f8c61cc93c5e81847e7f378bd12633cfe6f17a25b1a96316c5b589eb10d61dec2b5835b03b6016bfb57deaf8d5ebabcb577eaedf5d82ba8d742ae315c02b7456e2ad835aa6b51d694acf9596eb21d619ac1557eeae8d5c2ab43564aac1d56baaa75512a9ad526aa2f53daa73d4c6a95d51eea245439a855504a9f453bea74d4e169b6d34ca6694c7298252daa5614a86944d271a4a148e290751e4a399468a8c55172a2d9452e899d12da23d441a87750d6a18f42e2854d09aa0f3413e812d00d9feb3f9a7e74fad9f2b3dae7ae4f4d9e473c2e779cedb9d753aae749ce7b9cb5390a70c4dee9bbf37666e54dbb9b59360a6ac4d499a3f34666854cf299b5330a6554c92990731ae62e4c44985930525fe4be497ab2ef65d2cb8d96fd2dbe5abcb3f962b2bf6572cacd954729c2527ca37943f281e4f7c9d7937f269e4c7c9659265248e48a48fc91b7230e455c89c912d21fa437c86090a3210a415481290071fd23f2c7d68f8f1ebe3cbc76d8eab1cf638e46f28da31a9e343465c8c65186a30145ea8ba516ea)) else (if i < 9 then 0xa4c10b8482013c810d3042f120804d26cf99a68e830b064d13064f112b838c8c95c1c6478c337043c619f82192b838c8c2e30c619ccc653198b824e33c5c10f29e2e0f83192e33c5c10f29e2e0f83192e53c5c1f06325c678b82185cc5c1c60894c678830b8c31862c08a1718630c5811718e28a060bb2392292076c8e47045254e591c51412298c730714c639c3257071919489467f1704c18c9f186771505822a51c9e2e0c98cc0c58c3318b822633c5c18d296672078cb378b83263302112b838c8ca44a3378b8260c64f8c3338a82c11528e4f17064c6589c54160d986c66062c619cc5c11319e2e0c694b3b903c66042c619b031e32cfe2e0c98cb378b832633021252cce40f198133478cc099e371b8a20500c04182804100c04102804102804168f45168f451310163b0822932c14c662302605718041f1b0410041e6018021c581000e0608008b2d89a1600b47e370a3028fc6e15584034e0e2f4e16338de20f19c6f1078ce37883c6038cc3054ee3058ce378bc01c9718c6711844e3788389a118ce20b8c09878d16632c61e308db73b99b4d4f0fa2574784173787d12b6dcba7f0fa0d79a9529e20bc30c09487290c5018a431406290f8210028e2f0c61b0d06429e2702b078a393c4e112290c5218a4314f10514f104e270ab0303c00e53c217801f4789211e8017043e6f1f8a22d4960f1430787d1c735e6e5f0f822d043a0060f0c304100d3c4100040e0867b1b8d7a0973498002c008d01700200006801d00207801f00231f0fa19820c7c3e86608001a00475e1f47304d3f8463e8e64a31f378f8994960800d0020435d6e77378e21e268d05c6db9dcce46d443c5e8a5cee66db6a21e8f14edb0cc43c46cf436a72e39dcd10f17a1a33b9e21e6f17a1b7339e20e6f17a1b5378a1f10295f005059ecd13821b3d9a2b658a2820f13b2283379af3f9b839435fa2826eaf4fa6f1f88a19ba34e50d378bd19b9b4d0b821f37a23714f14ae08635cae0e9fd0ec98083c50c1c186001c10b821800018360898360880f003e3e0ab328201a00402d787d1ac109c08b797c6e3f8fc430cd51c61871fc5e8cd4dc785c10f1bc7e288b52583c50c1e1f4718d79a97c3e08b410e801e3784a3e8d64a51e378f49949607043c6f446a29e295c10e8635c6f43b25b04360860838de3f10c3a79a1861c6f17a3a79a9b8d0c1dc1060f1de163fa2d9861bc30c104034f10400004000100000000007001e00200007001009c080001078a183430c007021e042000a18543080028781128781100000005010a02140428086c1f3f9bc42d183a3993f301f142cc078fc6cde685be2f18c3994f0a10d031407400e801704290b0051484200c5010873224858224a4250d0445486160b8228142ec8e00c29e20ac8e08a06022dc9604a09e7f3633d1e2284c8b043 else (if i < 10 then 0x35f885f103e20521e208224ae0f8a448b28c5c191cdc188cd41608767e0c44a3270630578826508a248f06255e9bc59b1237a6e0e9e45382e68a0514f104ca712bc353f0427629dc4c11022ca517044250882cd71fc3c69014020b47a28a03a038c419a88c101868406020bc118080e028b8e09281e38241049c402386cbe3f8b34246b8fa1e3491aa3449a6305e205c8e109a8e270c6040084d4b60080227881634394f071bc2200c0417822c101805113c80460d8c0c538c1453c412a9c4ce0d8da109d8c6712844e9f1bc39a901408186878c0f181cd32f8de21235d3e36864c3c2138338dc52002405c8e109c80109c8e109c8e10822cc08230b3384100210200426230426200426230426230426243a6d104a6d105a6d1040106360810021054c91471c9e008480a3205e2e6451c72449cb358bc12270b614b358a5e6788b61850a21788b6105489131243131243129f44169f44169f4411734fa2f0485c4d0534fa294020c681020042e6789341851221789341730101c96109c80b981b3822485982a0808010b9808001f1022484000b51c81389c2155399e2b088d47204e27085ccf178636a733c4e11399e2f0c6d4e6789c22733c5e18ea94cf17844aa533c5e11014040804010814040804010804010804010820cc35461035458bd2458bd244cc1570832502248799e2f0c7a71278bc3200802173385c18c00014040b99e2f0c7ccd378bc3203c1660a82ca73385c112280c5018a0244d08490055903051102485882ca733c5a19329ccf168642100420a2429762008a117145237245028a32dcca11228cb73a8440852ec8a1903ae47045248a04596e21399e24a0690b10494f1044f05216609294fb306248799e2f0c7a61278bc32733c4540ca1a208a9e20804010b99c2e0c60000a02040e04a1a7091c09531da70f99e2f0c7ccd3f8bc3233054165399c2e089ccd378bc320050d30454c76983877304dc2e0cb8c85c8e10b180e53c58c8f29e2c6471408e31c45414220bb2391c32d91c4540e280bb2390a82c5318e6708914c639dc221762854b2391c134502364713845b3392c51e305567f178454a393c5e111294fb339040a59dc96113190e33c4508fc58c08298c7338a40a788c38c93180d9dc9628c298cb3d8a4c60aacde2f08a947278bc222529d67720814b3392c222529d667208e371440a018083050082018082050082050082d1e8a2d1e8a26202c6610452658298ec4604c06981c5e9820022cb626858028041e601c021c601000e060b85a6880e16634c1e338fe20f19c7f1078ce3f883c6038cc3858ce3f8bc01c9718c7711844e3f88389b128f620a9d660821cc7107cc73b983e639dcc184399620c2062c0c61031606388029c41a42cc1242ce105c1a0c3ccd3e98360c210d3841706830f334fa60d830c998310e else 0x3881b103e205c3e208a0e009530b47c2d48da2d0f0c6e6f0c5a7f0c5e10408010815e20814020814020814020bc4098a13142628737c6f0f1e4050082d1e8a280e80f31066a2384078817238426a389c31810021352d8020089e2068f0e53c1c7f089c20422c47086e605ce08a804100ac2130a11503a6074c0e5342420c420841c9e20ed9e209c9e270064d7285da21))))
def layer511r9 : Packing := (887,4,5,63,0,15,1,packed511r9)
def keys511k10 (i : Nat) : Nat := (if i < 1 then 0x73782626300004a08000c24b848ea1be633138f1fc4250536b12f3fa51496e8cab8d024a1f6800a8a3f5c172adb09636f9116b1c63c28b8dd721d0739c51c4c4e8352b79a85000234702e68bde9c7ed6a856326393f5a0c9300000002d3bf521b19d53b62636e3163e4986ff000173d58f3f00aae012451dc15fd156edb282398d551fa7a33e3a0ad0702350653878000247479a4cc31332ee2b2519c43cc0000234817295be6538be76d0b9cdb3ab90b727000096c9ccba41864954f3694296b6d02f01ce0506023d88208bd62bd5560fe8bcb03e38b236d7131dad0320627f0b7dda6d0181554572e531e4d40ea469548407ee1b08d4cb14f40e9e3f6a459812754fae7b085b219bed80fdaf4b254b5a6790bf4c2a9b198b61611d1b0528bef266ad81b5b2268dd62d7d54ced2a459c58175201ffdd89a0c000c6e44bbf5aba65db0cabb94616ba3838851b52d70ba33752b54d69b37a98c1f995cc1a59e0000d77253fa9bcca3d3c836e87df45ec97b4cff2acacb8af0000826473c1278000d9d8f4b96dc00053394f3000001b59771eba56c000f1944106b5164d8088000822f5e1000333429b80000001c69a50f6746a831e6c894317a54d312630b292d2965b5d9f6c90c1cdafe636c1ee471fda88067c72db3ab63b3be5e352ab0c0a8f46a427a871bd37c9444a2d15ada9c87cfaf40000003629910fb6a704823b9be3217c2da1894a38000f6f19073913f3117c7ad39cfa41430a2db0d1f59a20002a98a9efb0619019ca8315a93000000000036bf147800000015e0a0cecf767f8a9040baf4520d0cf6d63d80a5c506e434dc6051967cdd931972095a5c4ae4bd596e235280cd44d6db7d3402b0c7ac6607ab02a2cc51f3031f53422552a62f2310eba3f038d5eb228aafa9a16da436cb6659a0000a9ebd63c409a5000058d081d3984000c9fc8f9f12e0c40000000f718efc561f875d642d36d24c000000000051ac000000334d000000057d848c00000000000ae69b00c5a110103180c000508001b033655050003091b020104a40d040415050a05011102201809170400180813270071020005005803040110001f04012c430f050709020f680104000400001b0a0100000a000917160a000401091605020d14000718220203000209060402010103052c002f1e11311a050320040000105800001103020406030b000a09000204000d225700091501051900321e001f081103010400310701040e01001900b11705160000351902080a000201041104120003011b0d310009140200070c00001c0c0020630e031b14051615030109110205090a26016c0a05040931140400002b130e0e0a22000004000007003312002100000a030b0001010a0103001f0809020200340019006d0100172f460053090701020203050001000000290003 else (if i < 2 then 0x8889d2f039d735a88c3ae5c1aa333a20015134000000252d87a5b0f8c681e71aba9f000000007390c49000034ec37a816188fe10d2e800054c5ad17b74000db5400093fd9d7f8f994db1f80688af9ae303c69c52277af68192e8fd0af66be7979d94013a068c3a904ad92d0fc9a91cbb0c3acdb062a3afd661666647803b2c0f69096800099ca9c91c27caecbc4b5a4699c20f64f9a15a2b750e02449b9c8c000ad0aeed4c634c7f8dd1a9000000001bc000895570da1a900800023282774ddf3830000a1b01d5b84bd03c6ca505d7d626c029bdceabb9cfb9891ca1527e18000036b2223b0e0adcadc36217941c7cc0003a5460713f38ac4875cb76c571510000000784ee0d3a7752cd0ca03d069c2497a1e1ae09d64e559c1633ed94737bbf6c4f435d5f85dd8871a74c1acf55d7495143e36a870d972c9318200000000000dde0000ec10000513a654584c35a65c0002a19f87c000b19c000384759935d3ec70002f6b4616e20bdc55420000000000042c319aaca1dd6ea8d5ee68913666f5ec322affb09232a7200769bdc4b11cd5677255ade4ad89458270bd27fcb06435467299225e89ca62f0e665e658614bb46e768c321ac782974b7fb33f483eb1a1ecef3c7c98da692a4d8011ed9b0429805625542fd4687746111ce18c7700621048a8b6efe301a239eff003a01c8252009186d173548667f42f0ed4431d217cac2da26295bf132ad3c3a6dcad3305b731174b2954cda81118b04605f3f563d7a407d45122194c1dab387bea564e8532f1724c97204e39d044c3fa17eea143ae178f86b0ec5920ddb495250d2a34de86cbb11687890e338bb701e5d529cc438483b48e5bd791c000b83ff440cec000286c000593b65209430872ad057d37ea00f34f800065dc0004ba743800030ee0002e6d6cbc5107850efa000005b00025ecd95a9fdc2d154a4d9a4d14a7c000f7e7039d5a2eb6a4779293b9c00095ff8d30bb0edcbc5bd7a10eca0265fa538b9e7a0b98a2ecf7980000392c000c7322b34753dd11d5695d7d7643c522102144d3e8c2449c980002911e6048d44d21c13f2592b555d800093d69620002acc457800087fd8867638cd5b60c000e2f96efbb15e3100000001b61e46497c00027b400059935c100030e2e40800019f3a1645612aa0003c8ae15a829e73e9fbf9450a90000f36486247a0002f41000186096a80001ab0000b660000ec4400b2aa509146ea46d6519e6228e185700000002dc2539215225bf29327e2d0f9a4e489508862356523aac2733729719c12d50059f99c0003b4f75242f4c9a00000001ae00001258329d880a56596b8c94c17546c6ebd3d2ca2d0348428d320a06ac18374db00af667d59df3e80000003684000072dcd9c15c418db07bce5ab792c8c7027f39c004013616496c848b4822a0592ed70ba80 else 0x28245))
def packed511r10 (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 1 then 0x3efa6660a00ff660d82802ffaaa5ca00bfe6a172802ff8a85ca00efea2172803df9875ca00f7e9dd72803df9765ca00fbe99972803fd9835ca00ffa60972802ff9a858a00efea2162802ff9a758a00f7e9dd62803ef98658a00ff660d62803fe98258a00ffaa2222803fe98788a00ffa21e22803fea7788a00ffa61a22803fe97688a00c7f65c97a22fb8a065187a7faa98721f9bda461c879bfaa99621f2fe8865887d3f61d9621f3de8864c879fbaa99221f3ee8864887d7b61d9221f3f688644879feaa99021f3fa8864087d7e61d9021f1fd8764087e77a21939df3de8864e779fb68a9961a7eda2261769fe680985db1fc9861d76cbf261865db8fd8721e66bb768c8799aeeda221e66bbd6848799aef9a021e66e3fa227799bcdda39de66bb768e7799b9bd8721d84baf69887612f9da321d84beb68887612fb5a121d84bee680876135bca99dd84e6fa2277613d9da39dd849ef2a677612f9da39dd84eafa2266613cbe7799984cef2a6885d27bca9a2174e6fa22775d3abe8899974f2f9de665d27dda0a6583af769e8860f3de8825d839f76809760ebdeaa61d83ee76918760f5dc9761d83e77a227760e7dca95d983e7761d7660f6de9999983eb7a226660f6dc9799983eb761e6660fcde7799983de7a658460fb9e8861183de725d8460fb9d8761183f679dd8460fe9e6661183ee7a217460fe9e665d1839bf69a9960a6fca9999829bf698985ca7f9a026172c7f261875ca7dca960d72e7761d835cb3ec9860972ebb6198258b9ed8721e22bbb6988788afcda321e22bf96848788afe9a021e22e7ba227788bdcda39de22bf368e7788a7eca961a22ebba226688bcee7799a22eeba218488bdae7761222fab9998488bbae885d222f6b9dd7488beae665d222bf3aa98388bbce8860e22bf329d8388bbcd8760e22f739dd8388bece6660e22fe36118388bf8d7460e229bf698985c27eda226170c7f261875c27dca960d70e7761d835c33f89860170e7e61d805c25fda7261609fb688985832fc9861960cfe261805833dca9a2130cf7a66884c33dd98a21309f76a0974c33de8825d30e77a22774c36de9999930db7662664c3ade8899930db725e664c3cde7799930df3a66224c37cd9888930ef3a22224c37cc9788930f739de224c3ece6688930bf6aa9704c3bda885c130f7661d704c3eda665c130ff2889704c25fda7261209bf698984833ec9860920cfe261804839f98721e00bbe69887802fd9a321e00bfa68887802ff1a121e00e7ea2277803dd9a39de00bf668e77803afa8899a00f3e9de66802fdaaa60e00ef6a2183802fd8a760e00ef661d83803dda7760e00fb699983803bea8888a00f7a9de22803eea6688a00ff260e228031f987640879f56849760e7d9a025d83c7725d8760e3dda825d309f5684974c35d8975c130 else (if i < 2 then 0x9ff2a5825c37ee9988970dfb662225c3bee8888970f7b61e225c3dee7788970fbb99a225c3fcd8388970bfeaa9805c37f8a960170dfea65805c3bf89860170efea21805c3df8a760170efe61d805c3df98760170f7e9dd805c3efa6660170ff668d805c3fd98360170ffa889805c27fda7a65609ff69c985827fca961d60d7f2a6775835fe999dd60d7f662775835fc989dd60e7fa2277583ddda39dd609ff2a6775835fd979dd60bf768e77583cfe7761960f3f9dd76582fdeaa60d60df72a583582fdca760d60ef761d83583dde7760d609ff2a5825827fca95c960efba2222583dee7788960ff360e22582ffaaa60160efe61d80583dfa7760160ff668d80583fea2260160ef769e884c3bdda6a2130ef768a884c37dca9a2130df7a66884c37dd98a2130bf769e884c2fdda6a2130bf768a884c37de8825d30bf7aa9874c37dca961d30ef7a21874c3dde889dd30bf7aa9864c37de9961930df7661864c3bde8861930df725d864c3dde7761930ff3289864c2fdeaa5d930df72a5764c2fdda85d930bf72a1764c3bde885d930f7761d764c3edd865d930fb7a22664c3edd8799930bf7aa9824c37de9960930df7661824c3bde8860930df725d824c3dde7760930fb7299824c3bdd8660930fb7999824c2fdeaa5c930df72a5724c2fdda85c930bf72a1724c3bde885c930f7761d724c3ddd765c930fb7999724c3fcd825c930df7a65624c2fdda858930df7661624c3bde8858930bf769d624c37dc9758930f779dd624c3edd8658930ff3609624c3fce8888930ff361e224c3fcd8688930ff35da224c3fdaaa5c130ff66a1704c3fd8a85c130ff6a21704c3fd9a65c130ff6619704c3fd9a25c130ff6609704c3fd9625c1309ff69e994827fda7261209ff2a5874835fca99dd20d7fa66774835fd989dd20d7f262774839fe889dd20f7768e774827fca99dd20d7f65e77482fdda39dd20d7f9dd964827fca9619209ff2a576483afe8899920f3f9de66482fdeaa60d20df72a583482fdca760d20ef761d83483dde7760d20fb799983483dee7760920f7b9dd72482ffaaa60120efe61d80483dfa7760120fbe99980483fd9a360120efea2160483dfa7758120ff660d60483bf9a7a2200efe29e88803bf9a6a2200efe68a88802ff9a7a2200bfe69a88802ff9a2a2200bfeaa987803bfa8861e00efea2087803df98721e00bfe69887802ff9a221e00f7e2a277803dfa889de00bfe2a277803bfa889de00f7e61e77802ffaaa61a00efea2186803dfa7761a00ffa28986802ffaaa5da00bfe6a176802ff8a85da00efea2176803df9875da00f7e9dd76803ef9865da00fbea2266803ef98799a00fbe21e66803efa7799a00ff6a2183803fd98760e00ff661983803fd97660e00bfeaa982803bfa8860a00f7e9dd82803ef8a660a00efe6198280 else 0xff9e885d183fe76197460e7fda7a65829ff6829960b5fca99dd82d7fa667760b9fe889dd82f7768e7760a7fca99dd82bf768e7760b6fc9725982f3f9dc9660b9fe77619829ff2a57660bafe8899982f3f9de6660bdbe7761182eef6198460bebe6661182defa657460bbbe885d182f6f9dd7460bebc965d182eef6197460bebe665d182bf7aa98360afdca760d82ef761d8360bdde7760d82ef76198360bede6660d82fe75d18360a7fda0a65729ff680985cadfeaa61d72f6f691875cb3fc9861d72d7f662775cb5fc989dd72e7fa22775ca7fca961972e7fa21765cbafe8899972f3f61e665cbcfe7799972f6f9dd845cbdbd7661172faf999845cb7be995d172def661745cb7bc985d172eefa21745cbdbd875d172f6f5d9745cbebe665d172f775d9835cbede6660d72f7b9dd825cbfad7460972d7f6627758b9fe889dd62f7768e7758b5fd979dd62bf768e7758bcfe7761962f6f9dd8458b7bd985d162eefa217458b7bd975d162f6f9dd7458bebd865d162bf7aa98358afdca760d62ef761d8358bdde7760d62fe75d18358bdee7760962feb5d18258bbeca7a2222bfbaa98788bbee8861e22feb6918788afeda021e22f7b2a27788bdee889de22efba227788bded879de22efba218688bdee7761a22efba217688bded875da22f7b9dd7688beee8899a22fbb61e6688beec8799a22fbb9de6688bfad8761222feb9dd8488bfad8661222feb5d98488bfae885d222feb61d7488bfad865d222feb5d97488bfcd8760e22ff36198388bfcd7660e229ff69e996037f9a0a6580aff69e886035fd9725d80bbf69897602fdda325d80bfb68897602ff5a125d80affaa9876033fe9961d80e7f25d876039fd8721d80bbf69887602fdda321d80bfb68887602ff5a121d80d7f2a6776035fe999dd80e7f2a2776039fe889dd80f7768e776027fca99dd80aff2a2776039fd879dd80bf768e776027fca95d980e7f61d766036fe9999980ebfa2266603afd8799980f3f9de66602fdeaa64d80df7a6593603bde8864d80bf729d936037dd9764d80ef761d93603dde7764d80df765993603ede6664d80bf7aa9836037de9960d80ef7a2183602fdca760d80ef761d83603dde7760d80fb7999836037dd93649809ff2a5726039fd875c980dfba6622603bee8888980efb61e22603dee7788980fbb99a22603fcd9388980ff360e226027fda8a6570df768e995c27feaa66170cff660985c2efda626170bfb688985c33fca9a2170cffa66885c39fca7a21709ff2a6885c33fd98a2170b7faa9875c35fe9961d70e7f261875c39fe8861d70cff261875c35fd989dd70d7f262775c39fe889dd709ff2a5865c36fe9999970dbf662665c3afe8899970f3f61e665c3cfe7799970bf72a5835c37de9960d70df7661835c3bde8860d70f7761d835c3ede6660d7)) else (if i < 4 then 0x70eff619825c3fdd8360970ffb649825c2ffeaa5c970dffa65725c2ffda85c970bff2a1725c37fd985c970f7f61d725c3dfd765c970ffb609725c2ffda958970dffa65625c2ffda858970dff661625c2ffda758970f7f61d625c3efd8658970ff760d625c3fed8258970ffeaa9805c3ff8a960170ffea65805c3ff89860170ffea21805c3ff9a760170ffe61d805c3ff9a660170ffe659805c3ff98660170ffe5d9805c3ff9a260170ffe649805c3ff98260170ffe5c9805c3ff96260170bffaa9875837fca961d60bff2a6775837fe999dd60dff662775837fc989dd60fbf9dd86583dfd875c960ff760d72583ffaaa60160ffe69d80583ff8a760160ffe9dd80583ff9a260160ffe5c980583fdeaa61d30ff7a21874c3fdda661d30ff7689874c3fdd8761930ff761d824c3fdd8660930ff75d9824c3fdd865c930ff761d624c2ffeaa61d20dff2a587482ffca99dd20dffa66774837fd989dd20dff262774837fe7765920f7f61d76483fdd7660d20ffb9dd82483ffaaa60120ffe69d80483ff8a760120ffe9dd80483ff9a660120ffe5d980483ff98758120ffe9dd60482bfda025e88aff6a097a235fda7a6587df768e9961e7fda0a6587aff6828861f7be9965187eefa219461f7bd9665187def6519261f9feaa61c87e7f6818721edfeaa61c87f6f6918721f7faaa640879ffaa99021f3fe8864087d7f61d9021edfda626277f6f690989dedfda226277b7f680989df9fca9a2277e7f69a889df9fda2a2277e7f682889df9fc98a2277b7f69a889dedfda2a2277b7f682889dfdde8864e779ff680989df3fca9a2277e7f69e889de7fca9a2277b7f69e889dedfeaa61e77e7fa21879dfdbda461e77df7a21939de7fda7a65869ff6829961b5fca99dd86d7fa667761b9fe889dd86f7768e7761a7fca99dd86bf768e7761b7ec9724986f7b9dc9261a7fda0a65769ff680985dadfeaa61d76f6f691875db3fc9861d76d7f662775db5fc989dd76e7fa22775dbcfe7761976ebf29e8899aefeaa61e66ebfa218799bebda461e66bbf6808799bcfca89de66f3fa227799bafe889de66f3f61e7799bbbca7a2184befaa987613bbe8861d84f6f2a277613dbe889dd84eefa2277613dbd879dd84f6f9dd86613dbe775d984faf61e66613ebe7799984eef69e885d3bbda6a2174eef68a885d37bca9a2174bef69e885d2fbda6a2174bef68a885d2fbeaa61d74eefa21875d3dbe889dd74befaa9865d3bbe8861974f6f9dd865d3faca261974befaa9765d2fbda85d974bef2a1765d3bbe885d974f6f61d765d3ebd865d974fafa22665d3ebd8799974df7a209760fbdeaa61d83ef76998760fbdda261d83ef76818760efdeaa61d83ef7a218760ff9da461d83f77a227760f7de9961983df725d8660fbdd8761983f779dd8660fedd8799983fe761d846 else (if i < 5 then 0x61f7fe9964187dff6599061f7fd9264187dffaa99021f7fca9a2277bff69a889deffda2a2277bff682889deffda025d86bffaa98761bfbda461d86bff2a67761b7fe999dd86ffb9dc9261bdfeaa61d76f7f689875dbdfda061d76bffaa9875dbfbda461d76fefaa987613fbe889dd84fef9dd86613fbeaa61d74fefa21875d3fbda661d74fef689875d3fbd8761974ff7aa98760ffdda061d83bff6809760affeaa61d82fef6918760affca99dd82dffa667760befe7725982eff9dd8660bbfd8761982fef9dd8460bfbd875d182fef6197460bfbd765d182f7faa9875cbdfda661d72f7f681875caffeaa61d72fef691875cbdfd875d972fef5d9845cbfbd865d172bffaa98758bfbda461d62dff6627758befe7761962fef9dd8458bfbd875d162ffb9dd8258b7fda7a6580dff29e996037fda6a6580dff68a99602ffda7a6580ffe68299602ffeaa65d80dffa65976037fe9925d80effaa987603bfe9961d80eff69987603bfda261d80bffaa9876037fe9961d80effa21876037fe9921d80bff2a6776037fe999dd80dffa65966037fd9765980dff25d96603bfd8765980dffa6586603bfd8761980bff2a5766037fe995d980eff61d76603fde9964d80ff7a2193603fdd9764d80ff761d93603fdd9664d80ff761993603fdd7664d80ff7a6583603fdd9760d80ff761d836037fe9964980dff65d926037fc9764980eff61d926037fd9664980ff764d926037fe9960980eff61d82603bfd8660980ff764d82602ffca95c980dffa6572603bfd875c980f7f5d972603fdd935c980dffa6562603bfd8758980ff764d626037fda8a6570dff2a2995c37fda6a6570dff68a995c2ffda8a6570bff2a2995c2ffda6a6570ff768e995c2ffda2a6570dffaa9985c37fda666170dff689985c2ffeaa66170dffa65985c2ffeaa26170dffa64985c37fd9826170bff698985c3efda626170ff768c985c2ffda226170ffb688985c3ff5a126170ffe680985c2ffda9a2170bff2a6885c37fca9a2170dffa66885c37fd98a2170bff69e885c3dfca7a2170bff69a885c2ffda2a2170f7faa9875c3dfe9961d70f7f261875c3dfe8861d70f7f699875c3dfda261d70bffaa9875c37fe9961d70bffaa9965c37fe9965970bff2a1965c37fd9865970f7f61d965c2ffeaa61970bff6a5865c2ffca961970dff2a5865c37fe9961970dff661865c3dfd8761970fbf659865c3feca261970bffaa9765c37fe995d970bff6a1765c2ffca85d970dff661765c3dfd875d970fbf619765c3fde9960d70ff7661835c3fdc9860d70ff7a21835c3fdd9660d70ff7619835c2ffeaa64970dffa65925c2ffca864970dff661925c3dfd8764970dff659925c3fdd8364970bffaa9825c2ffda960970bff2a5825c37fca960970dffa65825c37fd9860970f7f61d825c3efca6609 else 0x5d12579250124a92451235922812189209120191fc11f291ed11e591d411c691bd11af919e118e91891185917c1174916d11599154114491311121911c110c910710ff90ee10e890d510c190bc10b690a7109590861080907d1073906c10669061105b9048103c902b10279018100890010ffb8ff60fe48fdd0fd98fd20fc88fc10fb38fac0f9e8f970f878f820f7a8f730f698f620f528f410f2d8f260f128f0b0efb8ef60eee8ee70edd8ed60ece8ec70ec38eb60eb08ea90ea38e9c0e8c8e790e738e6c0e5a8e4d0e458e360e2a8e1d0e158e100e088df70df18dec0dda8dd30dc78dc00dba8db50da78d980d888d830d718d640d5e8d590d538d500d428d3d0d318d2a0d228d1b0d138d040cfc8ceb0cdb8ccc0cba8cab0c998c8e0c888c7f0c6f8c6a0c5c8c570c498c440c328c270c1b8c0e0bfe8bf90beb8bde0bd68bd10bc18bbc0bae8ba90b9b8b960b848b750b718b660b5a8b4d0b3d8b380b2a8b1b0b158b080b048af70ae98ae60ad88acb0ac78abc0ab08aa90aa38aa00a9a8a8b0a7b8a6a0a588a490a398a2a0a1a8a0b09fb89f009e089d909d389cc09ba89b509af899c09948987098189700962895d0957895209428931091f891a0914890d0907890408f688f108e988de08d888d308c588c008b888b108a988a2089a8893088b8886087e887908758872086c8865085f8854084c884908458840083c8837082f8820081a88150811880a080287fd07f387e807e087d907d387d007cc87c907c387c007b887b507af87aa07a28793078d87880784877f07798776076e876b07678762075e875b07578754074c8747073d8732072e8729071d8710070886ff06f386e806da86cf06c386b806aa869d06938688067a866b0663865c064e863d062f86240618860f060585fa05ee85e505db85d405cc85c105b585aa059e85910585857e0572856b055f8554054a8541053785240516850f050784fc04f084e904d984d204c484b504ab849e048c8483047984700466845f0455844a043a84290421841a0410840903fb83f003de83d103c583b803a6839b038983800374836b035f8356034c8345033d8332032a83210317830e030682ff02f782f002e682dd02d382ca02c282bd02b582ae02a08293028582780264825702438238022a821f0211820a020081f501e981de01d481cd01c581be01b481ad01a5819e0196818d0185817e0176816b0159814e014281370129811e0110810700ff80f800f080e700db80d400ca80c100b580ac00a28099008f808800828079006d80660060804f003f80340026801b000d80002ffda025e88dff69e9961f7fda6a6587dff68a9961f7fda0a6587f7f69e9961ffdda3a6587bff6829961f7fe9965987fefa659461ffbe8865187fef6599461f7fe9964987dff6599261ffbd9464987bffaa990))) else (if i < 9 then (if i < 7 then 0x7b2671a66a2664a657264da6482640a6352629a61e2614a60d2601a5f625eaa5e125d5a5cc25c6a5bd25b3a5aa25a4a59b258fa586257ca5732569a5602556a54d2543a538252ea527251da5122508a50324f9a4f024e4a4d724cda4c224b8a4af24a5a4a02496a48b2481a4722466a45d2451a4482440a437242da4222418a413240ba40423fca3f123eba3e223d6a3c923bda3b223a6a39b238fa3822376a36d2365a35a234ca3412333a326231aa30d2303a2f822eca2e322d9a2d222caa2c322b7a2b022a6a29f2297a28a227ea2712263a2582250a2452237a22c2220a217220ba20021f2a1eb21dfa1d621caa1c521bfa1b821b0a1a32197a18a217ea1712167a1602158a14d2141a130211ea10f2103a0fa20eea0e320d9a0ce20c0a0b920b1a0ac20a0a0972089a07e206ea05f2055a04c203ea0312029a0222014a0071ffb9fee1fde9fd11fc79fbe1fb49fad1fa99f9e1f949f8b1f819f781f6c9f611f539f421f369f271f1b9f141f0a9efd1eef9ee81edc9ed11ec39eb41ea69e9d1e8d9e861e7c9e731e6b9e681e5c9e531e499e401e329e271e1d9e121e069df91de79ddc1dcc9dc11db59dac1da09d971d8b9d7e1d749d691d5b9d501d489d3f1d379d2a1d1c9d131d099cfe1cf49ceb1ce39cd81cce9cc51cbd9cb41ca89c9f1c979c8c1c7e9c691c5f9c561c4a9c411c379c2c1c1e9c171c079bfe1bf29be91bdf9bd41bc89bbf1bb59bac1ba09b951b8b9b841b789b6b1b559b4a1b3c9b311b279b1e1b149b091afb9af41ae89add1ad39acc1ac49abf1ab19a9a1a949a811a7d9a721a669a5f1a579a541a509a3b1a259a201a189a131a0f9a0a1a0299fd19f599ee19e699e119d999d219ca99c519b999b219ac999b1993998e19869981197399621950994b19479944193e992f19219914191098fd18eb98e818dc98d118c998bc18b898b118a798a0189a98971891988c1886987d1875986c1854984f184b9844183a9835182f982a182298191811980c180697f717e597d817c897b717b197aa179c979717919782177697691755975017409733172d97261714970116ef96de16cc96bb16a996981690968b1679966616609659164b963c162e961d160b9606160295ff15f995ea15dc95cf15cb95c415b295af15ab95a61596959315859580157a956b155b955815529541152d952815189515150794f414e294df14d394c814c094b314af949e14989493148b948814829475146f946414569443143d942e141e94191409940613fe93f113ed93ea13e693e113d593d213ce93c313bf93b413b093a513a193921382937f1371936e136293591351934c13489343133d9338132e932713239320131a9313130f930a130492fb12f192ea12e092dd12d792d212ca92c712c192ba12b692b312a1929e129892951287927a126c92 else (if i < 8 then 0x21cc8d999c267869a1a7069e982a6049f009a3a6869e9822aa6089c87003320b2624c020349e9a842c0268a84127a60a9a842a6859f00d23c00698121a60a9813386981338731898636461892c9991824cc6362e1e0959e16761086c6ba388d25d4e7e6e12be89ba38a523e1e86c94905b886fa25251b1ae8e294946f878853a06a61b1ae8e2949463886ba25251b1ae8e294946b878853a06e61b1ae092e2949b8b87a25241b1ae8e29497846c538ba06a61b1ae1e214e8ac9fa38a423e8e2908fb31f8b846ba26d4ec0ec7e2e111e8a3531f8b87a06a6c7e1e2e81a978b845ba0465e1e2e834906f8ba0d2418e21be83494c86f8f88d25e21be834938f87a38a4e2e8308f8ba0c231be1e8cc1a946c6b33a0d051b1acce834146c6b33a0d051b32e31acc34186d306ba0d25e84c348f8f0b87a3325e8cc308f9f9933a0d25e7e6cce830970b87a3324e3e1e8cc910b8533a24d4e63bc2e73ae14ce8a6438f0b87a3326e1e8cc8fa153323e2c114e86c946c6ba389525e2e8908c738b9f9843a1b27e8e2948f9f079a51b3a2691ece7e6e2e8109f07a38a524ece6e214e81b9b07b29f9b8853a06e8e2c1e854906f8b07a24e241e850938b07a1524e2e8548f0553a2b241bc11ae8ac966f9d066ab3a1427e61bc1e71aace854a3a2b15231be8ac8f07a2b2524e894ac8fb03f8b846ba26c6e2e11be89753b03f1b8b8447a28d4c6e2e1e81b9b1b878ba06e5ece7e214e81a9a87b31b9f8853a06a8e2e118e811941fb01b8b853fa23a8e1e2e834905b886ba0d251ae2e83490c86b8f88d25e21ae834938f87a38a4e2e8308f8ba0c23a7e2e11ae8978b87a23e3e1e2e8928b87a2b24e3e1e8ac9387a2b23e1e8ac8fa0d2b23e1e8ac8f8a87a0d241ae2a1e8938887a0c24e2a1e834938ba0d23e2e8886ba1b23e8346c8f5384445ba3326d4e11118e8cc986c5387a3306a6e7a1e614e8cc986c6b8a879f9853a33291be2e18ce81a986c6b88539f9b8633a29c7e11ae8cc943b871c47a3326e116cce81196331f8b87a06a6e2e85c8f8b33a15245ccce8e254979f9843a3325e281e8cc909733a38a52454e85c8fa331523cce2e88d07a331424e8cc548d53a1723e8cc548f338ba2341e8cc5093a331523e2cce88fa2325238cc1e8e29494738b079f985233a28e2c1e88c94978b07a232525c6e11be8cc943f871847a3326e118cce81196331b8b87a06e6e1e8cc3493a330d23e8cc348fa330d2332e3cc34932f8f8b87a25e8cc308c8730aba24e2cce1e8938f8b8733a25a1cce834938a8733a2421cce8309287a330d24e8cc348f33a22e2cce1e8938f8b8733a25e1cce88f33a22141ae71be6e2e1e8a3b39f98344389a27e7e6e210e897b39f9b8843a26e7e610e8cc979f984035a33268ce7e6e210e89a6bf26b7a6b226aca6a5269fa6962688a6 else 0xd8218ba4608c778b84524a4608b8d48412b87833064241a00d484129128102694c2c10c3c381b869fa33274acc890906803c2c1cc8c6d92812e454c2c10f9f98538a87a3327114f4e4746e8cc94a2413d391d1b8a87a332994c2cc8c6f9f9b8a846853a332994c2cc8c3c381f869ba33274acc890906803c2c1cc8c6992812e454c2c10f0b0732354c2cc8e3218c1b1ae8e2549a52322e2e18c0e3250214e28c0c6c6b8b87a2315271be7e61ae214e1e88ca4523221b948c8e6e6b9f9a33a3895281b1ae8e28c54986a52323340e061be1e8cc1f1f846ba33250ee6e11be8cc99290b80344c709190a80352104b4a4744a040a31f082c2c708443c3b339ba388d284241a00f339ba388c25a6608b8d822c2c2c7093b986f33a0d26c221e6cce8309b9f08d39a87a3306e7c2c70858402b8733a06c6281811e116e8cc9b1f082c7c20b0b1c28c878b1f87a2306e68c878a33a31f8a6e51a8c870d71895035c62670d7189983e7e6e254cce8319c2a8970317a7a6a2e8cc5431209c985fa38950c4730cce617e2e8319cc3309d985f8ba0c68676681e2e8cc909cbcb89c9b8ba332528e7e614e8cc95827225c9462cc10b82a9f8b33a0ee7a6a70a9e9b33a150ee6a66009069e9ba331426a6a70b73529f8b33a198ee82ecce83b9414da9f33a0ec51726e8cc94361848ba9f33a250c679ca708e3a330529cee666e3e236943b99718b3235c5488bc2a9b8b33a0ea7a7a60a9a9f33a150ea6a76009069e9ba331426a7a60b73529b8b33a19cea83836e2e867cca69e9a12fcce83a9414e29b33a0e851727e8cc94381848be9b33a250c679ca608dba3305298ea627e3cc14a638361e7298267e3e238943a9a9811730e2cce83a9a9b8f8acd50e86a6045e9b33a150e86a641e8ccb3509a981cce2e83a3397338ba0e8ce55c62cc8d715226785719c26766e2c1e8948c9d9d9a3307a38a5271d6766e2c194e88ca0719d9b0633a38a5289467e68ce8c1e29f899d9b0633a25279467668ce8c1e29f899d9b0633a252766e2c1e88c94739cd03c1c6b87a3307c6e11be8cc943c1f1b846ba33274a42e00d131824742a00d48412d29191281028c6c20b0b182110f0ecc07c6e8e234a50906803ccc7c6e8e2309a0b18218100ae1cce81a16a058478463a3326c6c20b1b082c2c6093d1f186b33a0d27c7c6c221cce8309aa31f1b08d287a3306a8c2c60b0b182a7608b8d822c28c878b1b87a2306a68c86886e321838ce8c6e29a961f18287c60a1e33a31a625a662618991858236762610d99898432221c08c88870032221c00ca88b023a4a10a2e9282334cc8b001c00590d02cc62618c90d02cca3a2e1e094d191843a786981a7a60a9c12aa7089887003320b2724c020349e9e842c0278a84166c0348f31898636461892c9d91824cc6362e1e095888730334)) else (if i < 10 then 0x8cc3198409d9b87a330c672f2e2726c2e8cc9422870a29461c48cba9f87a330ee6a6600a9a9c2d4a7e1e8cc663b1cb8efa3325059426e1e8cc3618c840b8ab869fa330c69a1a708e05387a29f30ee766e336cc943b9987122c261540dad9d9a078ba1464281b6b67661ac1e8e294a5ad9d9b8ba306506e86b6667e2e8c1941aa06c699d9b8ba305b282f2e2b2726e8e294a1ae906f07a38a506a89b9ae7e6c1946ce8a18906823a6a70aae9d069b8ba1426e8ab1aa7a6e2c1e81b54a69a9c26441548d406f046ba2b266766419451e8ac9d9d9ba2b2516e6340f0b07e2e1e81aa0403c1f8b846ba1b284ae00b1a1c7071f1820f0e0b07e2e8349f2f1f1b8ba0c2664e2e81aa7749b1818760868c582c138b846fa06281b071a1c7c609591f87a06b1ab071b053f1b87a2b16a6c7600b1f182b4c6e1e8ac675a1d615b87a19eb31a7c6871f182cbc621c7e2e8309aa32c6f1f1b8a87a068d29c7c608691f891ba1615a71b071b1fa1b0d26a60f0a0706e2e11ae86ca4402b1b8b846fa1b28608787a31a69b25524ac6e1e0951d0680352104a44a0409b041180b04e2e11ae816a21f182c6c1086e811a3c1070580247e8acc6569a1b071824f5ae8ac9416511f87a2b160652104f4ae1c6e8ac51a7071825614e1e8c6ac5a9c511fa31ab161587c1c608511f8ba3195a687c684429d823a7e3986c549a9a801c60718141c60b1b8ba34cc25938718110e15ae8ac17181c6e1e8ac5a17181e15ae8ac5397181c6e221e8d3309a9f1b8f8a84d06b4e7c6071b8db0d34e6869387866ba1b24e51a64616010a88b023a4a10b86134e28990d0262618a8e8b878243464610c681a7869e8421ac0278e8416261899186227466460918d8b878241a61a28e918f878241a05859c261a48a8984d036785859c26421348c68167843c381c18d387a33284c0550442cc079b886fa330d26e7e6e2e8cc349b9f886ba330d26e7e6e3e268cc349d825228ba4608c538a214c2891cbf886ba330d27e21b1ae8cc349918bb886fa330d27e3e21b1a68cc349d290b80341cc08512d9380494c2092b0b3030f0ecc0706e8e234a06c6b8ba330d061464a04b131f1b8ba330c260e0a06a7e1cce81ba0538a9f87a3306e741cc0b0a14b64a05491530b303e217cc8d6d68519d9b8a87a332917e20b9f9b887333a0c275b5a6766e2a134e8cca4739f9b8ba0d3327e2cc085330859b8ba16e7e2cc0b0807323504f4e4746a1e8cca30a842c7c69b9ae221e8cc30a71f1b8a846c68d3a3329c2cc0b0b30214cc21a7e2e89a9c3c281e9b8733a06a814e2a6e1e8cc1a9d07302c2852d928152454c2cc0f0b322e2cc0b0b302100f0e0a0706e1e8cca79f9953a33250f0e0a0706e1e8cca33211a0fe6e2e1e8cc9c6c3b9f8b87a33274241e00d2b3226454083c381c1b8b87a33284241a0 else (if i < 11 then 0xcca262a161a7992d938b8640fccc2c193309b8b864cce2e18c3e10f4a07a644969909069c48f4ba66493329b8b864ccc2c10f901f0b06533254a0744a10f16509b0b04873063287c2c120cc2794a3310a85069c54b64c2c1a114a79d9b0b0653305e294cc8e50878b3241de2a16094cc98470988865332694cce28e53319b093e52a06e2e1cc95503819928a846322ae2e120cca69f32898a85869a64b64e2e193309e898a85869a754cce28c3b330b064cc27e2e193338b8630e84392a9c19125a74241a612392e9d924ccc2c10e913e3b309b0b06654cca7c28e97329f8b86406c2c194cc95281912843859427c2c121cc18ca1b0b0483309a528cc42a141a6152d930b0684529a71447c2c1a6159f0b0653305cca6e2e1904c392a991050eccc2c1904c3a990904554a6c2c121cc1a392e999248eccc2c12695524e3b329b0a60eccc2c127944586323e18c54e29152523235d9454e2608c9a51518984463266261548c138386315041b5466628c9652338b8644f66948c9184523231a5467628c9652338b8644e67948c9184523234e66948c903ca81f088a511e140cc90a81f883100f44a3a2943e1d1a8e890a65211104b4a4744a3a240aa2e998d8a44fc298a692621f0a5a9a5c7614f8c123189871e4c7e2604f8c946e321d1d8d8a68ce2c78cba321d1d99855a731cc62949170c58a725255c94cc66917253319e43b54a65ca794e9529d729a53acc67a69170d89ce249c3826369150ce9970ea50e2a06c222944785033242a06e20c4039128e8a50e4786a3a242994844412d2919128e8902a0ec6638262953a1c9f1b0a5a65847c256c6962e9d8d8a4c6614e8c123189871a4c6e2604e8c946a3219198d8a68ce2c68cbe3185631a564619896c6949d8d8b1a42221340c9087803e0548bb39f9ba38952611100f0e0a0706e2e1e86cacaf1025b67665a54a2e1e8aca786166e1e85bac969f87a269b251462e18d8985b2394865211b2b6766641ae1e2e894a8443c381c1b8b87a2b252a94e20b8852b2326e00a50127e008a88b8036254099d898436662610db18984354640888870032221c00c8885b036290886c6ba38a5254a42e00d898420f0e0b0706e8e254a08885503229408429284394e189ad9d9ba38a426340e0b06e2e1e81ba040381b8b846fa1b284ae00b1e1c6071b1c20f0e0b06e2e8349f2f1f1b8ba0c2664e2e81ba6749b1c10e0a0706e2e11be86ca4402b1f8b846ba1b28608787a31e6db25524ac7e1e095190680352104a44a0409b04110a6608c6d91858042a22c08e92842e184d38a264340989862a3a2e1e090d191843114461e01044c0bcb8a89c9b0b87a332ba1c208d014261a08f128f8782461348a9a9c2a160086d870a3c463e1e0910985523616789859a2e7e6c2e14ce8319d509c980b87a330c4810e6e1e else 0x34e2e16c11518788367e2899b8a2546ce28d538a21450e261904440ab85b38a6540f07a662a119448b855245150e18d9b862540ea70662a1189e85869a4a7e188ab86b23540ba262a1959a8a85859c567a2a161661591878a5044ae1e20c3f0f08888650ec3c2222194430f0888865340f226c90a81f18883c59bc6e1c790a81e2100fa3a2903d1d8d8a4c762144f93871e26c6261c790a81c8b043c594e0c7e1904784d30a430a3426190bc9e998e431e1c29412858650c649466c2e112519f0b84454a6613ba714458b04c24626cc10cd03889b242ac706220e166b1f871a42a0688403a8e8a40e466362909e19198d8a51a8664619896193b1d198e434c7615ac6156a919f1a456476158931988513a4e1c689b189871a42a0622c10e1653831b8641464c1a161a7c61d1e9383871855846c156904c38ab18885d3c6e19a903a8e8a313636286914d3b198e43453c6615a144d8d8a1e4cce1898333863cc67e10f319b8431110e221cc9785302102ae2cc9041928a85865108ba46461a098d047318a52511a464618b946e5199873251a946761cc94ab088a53325100ba444a1419a91898650465a44441a0933388d031044a3a241943c1e999289846a6a26261a7152e999289806e61b344ba664a2981e9911043c58727a6641b5498473388d240f0744a1419453806f8732551e221cc105d4733884cc21e20c738b323cc66e20d6f319b899c5cce25b8c478887304cce2a10f08873230ea70664a2611a9e8989869854ba764a2601a9868d12e9d928a6cc27a262a617329f883a70644410e169e189990695261a26c23836966b329f8a98511cce234903819128506514e01ae1cc94533308e0da986cce29a8c4c3a9911045a6641a5492cf329b8a68554cc8953322cc67668f319d9a311102ae2e1cc9844ab8b873250fcc0726e2e198514389873050ecc2706e2e19951938b86466e2e10d9f8b843112ae2e1cc955045928a8651027262523cce2e1a27550462e9192825289d8ba46261a0949c3f338b859e5e2e1e0cc93898781533250ecce2e166978b878332419e2e1e0cc94678b878151326cce2e18f8b87323e2e1084529128a865a242a1419153088b04873065411e2e1cc14403f088b0487327100ec222c121cc9c458853324a464148b90762e919180526104ba46261119999873236761cc8c47088b0653326110ba444a19498a81f8b87325540f0764a2a118c8ab8b8483329e7))))
def layer511r10 : Packing := (991,3,5,63,0,16,1,packed511r10)
def keys511k11 (i : Nat) : Nat := (if i < 1 then 0x6e32fe033445e68b87e400025ace2fd207da027770076457c36038be088333ce33806f08ea6ee8379451b53dea6761ded9940f48c8af33c7831713a4c45263be4eb2f432cb30fc000362b02f42b93070000eb15cefdd8c4bc000000077e1762000030c00002cd21fc85b00000000003ba55e5c72055b80000bdc458d81239e0001da2000006dea958822e346f8f8dfc15351ddb30003305c57000076a800039addc720fc017ca9bf21013d0525ea00008e57e582ada578ee08ae9f1d807200011b8c3aeb4c997c2647984ec65e60cd10de000000000002483706c79c0008f37ccac0b000000000003594932000328594ba1dfeeed97ef2b8000cecc5751ad72df08a1e606893a307a7e9e6b29aa5b219b6f2a81a76dec7200b4a03cb770e4832462bfdcaa836dc9656bb0bc0e2546f5563b00c0044e306f89d469ad10c7ad5e0002008ae74000703b0dab3d17bc461221c0000ecee2c7376b569b180000000000265c9649118fd2c00039fccf171827cb0001643ccd22d8d24877e00000000ea975600002cb4f62d2cdec6b870002e9000000009bc3b4f553e701c9b4000866bc895b6ef47c5126e6474800026f80000003ba9bf3c000023177d8a48d6cdaf412ffa2326cd4a9b926906cce3167041d15ca3a91256a2e440dc177264b4146d5ac6217f7c2ae9b30c08a87389baeda0da3903682ecfef417602a679963326bd38ac5f1290002bc2e9274214e7ea5e261bce94151f36ee66f908c299e90002d57ba10000889497fb0e18f0000000000002d78be733942a0ca27b530de53594984d6ccd885875ec0001b5428b7f530000000000049706417c4c95f06b7b2716d021ce4d36c7471f20db0fa3080000003404e538000cc8c000ef504940002d27b3e49ff0002537c9e29286bfd2f6927b4dfbd5c000d14d8b636a5ad239c0d410001c351e8b429ae2a5fa684aa33c259cea95a8a994552ab30903070100007b000a5e0000273e0108030207011303240900000b0500020007000210080700150009000011150914000000054209070f0c02074005030f0417050610370d0001000404040807080000081c0915164002002829180d00080c130314100112350e2f1c050003070d057500050c071f0036030f000f0901040500041a070827090500030000070f1f4d000e250002000b00051b090004030408180700040808131016060e050403130241060a00020b0700100380111a02030200321034000703130d271a02012f28031d2000090100510a01090002000048006406003000020001161e01082f1d081111553d0002090b0305042701000b02091300000048000606040505000220000100001b0000145a6b0a171e13610b09011f0200100c231302000801156d0500080802040c000116100014020400014c0013020f0306001b0409022f else (if i < 2 then 0xaacf6ff44642e7421b44fc8a84a92415dc58f30a14d804b9f72a24afaf9ec00b9ef2bc5a228d4d08bd6e8300cdf4d14503d20e27741a64f40f8000ef4334909a3d235900000092ea6f6cb8269cd55426ab4c000e6016896372b1fe786e7429c770787adcdb072ff71b5742469dd72adbc27a45c4597c68d6121f06d399b247c000cca041edb4380144da32d97d01f0000000094cc0004365253e99a63655ea15133981ab40ec33d78ab27500461afdf68afa8d4793e2de476b0000000970ff6c55198c5fc969f5c5000f701b3b85c8f7bc72386acf869da2e2d3571162cdaa963d800016e79774351db2d6247c8d997d228e70d2de31fef3a147aec6801aeed7f39973043cfa000041fc2ea88829fb080021847da95400088880001e4ee8296462ae4759f5cbefd87a9a292b727bcc2d37bb58335563af747bc23ceb5065815a512210d732c8d393aa323d399598e31b4525218ce8620cb7a6232a7215f80e8f8810aeb8cc817f2a4132d9300017cc00000008615d31603f73e7d3b0a73bd698cc4fde48ab900000e99bbde15580a4dcc170e177fdeb1716cc53fda1659efa4768843db2da8dd3cd922aa52967ddc708553c3a0bb810f6313583cfa3fc3afd179cada6154b0e77790806e78b8252d85002b2a617266ee79180d3687f93b33cf6f68aad1dedc6586258bee503a1df0c96f69f23666d67ad9247389927c6a32ec91b0285c723f8eba58fe1a96bfa397d3cf84210950dfc1d9b74b14d080d0f0620959e67372fdae35c565edee0161da73d5582ef785f9eab1d112b57cadfb1865a388a1950247607b23438af453bb99d060b05a42464e4622d878e2ed1f321c05813e00c1a996befdeddf209ad2add0a23d5b00c67b359e906e201fbac76d06d259ce3a8ee76778b1ed03a747fb4f80102bb7e508a91af24812c86b6b448b02b2e3d7d98681e731bcef84e6cfd1cd1dcba6add7e0c647d956976d85ce7c4875a0001814bbc533756a0000f30caa331a40002c9a82ad52ce598d1800082d717dfb0b1ba00012155853767f41c0000001693c06ea11c0f01306186aea111ffca6f1496745d371584d7e96332ef1004770aca3274755d776e10000000300c0009ac1ca4c42c0003374c7b9e19868828c000a89800000000007db9ec1a2ac80d32bced6649aae8076c0000000000613789c130000061f393bad947d719e427af828000c402a9d411bc9b00016a410c7e563c340000000d0ac638000fb280000d7a5cc877b58ddeac000024d8c4d3cd1a4d5800005541e9ae75605fc18a9e5378e70bba78a29098cc5ebd014fb4d48efb2a3c2395e3e252bed7a1b72c21b70000027540427d383b9da534194cde83e44f064fbaaee709d6aec7d316fea7752548bec834000c1209fd0000000dc740004c6d94d7c1000093f650c00020a075cc000927f4 else 0x1543c3b5eaf42b54d256f240007b65628e3a02f898bb272a875ae4bafac43a9d4b871910d3e7a0afc0001e67c7810798cce9c80002818c52b28c0e129a125e7e94c04e77435db199f744298ae58213575d00c28d4bc06c6aa030b5400061bc000cf3aee59413c8e0058000712fb5073b315b510ad0d00037168ca72c8edff5a3619c000167e1190001aed65f1005000100900031a555155646dc0f9b8977e97235ed9600017d96752124987b7b64117efea8760b274f54d56213cf2000000048f87810f0568170a26e36942ec367dc00055216b1e908abc6e684244da608da18c69583801cfbd156a85c03aac85639c0844d1adf))
def packed511r11 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x4c7d51e787601cc07001b2468b193461617985b6163455d14984e112a8473110c40c0f543ac0dd43370c1c2d70a9c270091c21e079c1b7063815704800e902e407b01480290003ff92f447ffa6587fff4430fffd9661fffb24c3fff64187fff444efffc9761bffb0ec37ff9dd86ffec3aedffc9760bffb0ec17ff9dd82ffec3305ffd7660bffb0eb97ff61972ffebb2e5ffd8758bffceeb17ffa6580fff44301ffd97603ff92ec07ff61d80ffe43b01ffe77603ffb2cc07ff61980ffebb301ffd92603ffb04c07ff5c980ffeb1301ffe995c3ffb30b87ff26170fff442e1ffd875c3ffb2cb87ff61970ffebb2e1ffd925c3ffb04b87ff5c970ffeb12e1ffc97583ffb0eb07ff9dd60ffec12c1ffd72583ff92e907ff61d20fff3ba41ffd86483ffaec906ff65e88dfe4bd11bfd96a237fb25446ff64288bfecbd117fd96a22ffb25445ff64288bff4cb0fbfe8861ff7b28c3effa2087efec390f7fd9621effb2443dff64087efe4c4efdfe889deff9313beffa2277efec3cef7fe9961b7fd10c377f9dd86ff64930d7fe995daffb30bb5ff26176dff442eddfd875dbbfceebb7bf61976f7f444cdefd8799bdf90f337bf9de66fdf44309fbd87613f790ec27ef9dd84fdec3309fbd76613f7d10ba7ef61d74fdec32e9fbd765d3fbd10c1ff761d83feec3307fdd7660effd32c16ffa2182eff3bb05efc9660b7fb0cc17bf99982fdec2305fbd7460bfbb06c15ffa6572bfecc2e57fc985cb7fd10b977f61d72eff3bae5dfd765cbdfcccb97ef61172fdeba2e5fdd835cbfdb04b95ff66162dff442c57fd9758bbfceeb17bf61962fdec22c5fbd7458bfbb06b17fb60962ff744445fed8788bfd90f117fb9de22ff6c3445fed7688affd32c06ffa2180dfec3b01dfe77603dfcccc07f764d80feec1b01fee22602ffd32b85ff66170bfe4c2e1bfe885c3bfb0eb877f9dd70f7f332e1fdd835c3fdc44b87fe60170bff4cac17fd98582ff930b06ffa2160bfecbac1dfe77583dfb0cb07bf5d960feec1ac1fee22583ff300b07f7a2130feec3a61fdd864c3fbaec987f760930feeb9261fdd624c2ffd32905ff66120bfe4c241bfe88482ffb2e9077f9dd20bfecb241efe66483fbb06907fb60920ff6b9241ff980483ff2c0907fea2200ffcc3c01ff887803ff4ef007fe61a00ffcbb401ff982803ff2e5007fe58a00cfec390f6fd9621efbb2643dfb64887bfac890f7f99021f3fd113bf7764e77beec9cefafe8899b9fcef336efa2184edf3bb09ebe6661377d10ba76f9dd74f5f332e97de9960f7bd10c1df725d83deec3b07dde7760fdbcccc1fe761183fceba307bee8888bbdcef117bb99a22fd6c2445fad7488bf9b07115f7a6530beecc261bde884c2fb92e987779dd30f6f33261fce224c3fb2e0986fea2200efd3bc01efa66803fb307007fa88a00 else 0xe2c3a26518b3e6693344d8b3e636d0d6899416a91d362c3a26504478e15533e6c3a26543c754c59f36199a29a848a1bc3a261aa0dc78c6b161d13283788d67cd8744ca23c6c58744c2939b31193e2c3a26506cd62cf98a4cd141a2d1d362c3a26506cd62a8533e6c23345584b68986e5201811bc333416a090a8f8744c353d4859b0e8986e76808b6199a0dce423638f8b0e899426c25b44c373342984de8985a78599a68986e63552161d130b4e631668f846683741c779b15cceeaa4cd151ccf9b41499326c57333b4f52668a4e27cceca4cd13a7c5733ba4d52668a4e26cee8a4cd13a6c4eaa4cd0ce7c26344c352900e08d6199a0c5048546c3a261b9ea478d0b0e8986a86808c6199a0d4e423e38d8b0e899410049f0ccd06a73752161d130c4f0b3b4d130d4c9f098d130d4cd0a6135a26189cb62cf1b08cd06a80f6a3611863416a1a67cd8b0e8993b44e9b0e89936898d234e991a2c3a2634a1a264f8744c99327c33344ad13a6c3a264c9d36199a254d86668672e7c26b61bcd8b414a730fd86b1682939bd99cd62d0527ce3b61bc5a0a4e6f667344b12829466379cd62d0527c7b2a67cd87168a3667cd8b4109b667cd8b41098deccd1f161d13e369b3347c38b4506f342ce6b0e899463699f36199a274f98de199a26a99f36199a26cf9b414992d4cc9f0ccd136ccf0736229a27cc6f641ce6aa62d14ec039f362d0427d9073e6c5a0a4fb33e6c45344c6f6664f531689f31bce6aa2cd13e7cc5166894d6ccf1b161d13e369b33c6c38b451b13c6c58744d9e31ac2b344cd33c6c2b344c6b6678cd31689f3e629a0e4b9f31499a25b98b3e6a93344e073e6d13084d9f36898525b98b327a93344f731674d526689f141cf98668293e2cf9b0ccd1363c4d33e6c333451993e199a25cf99a4cd12e74d8666897957e42f8c6e22384ae0337b2ddd371adb1f67bd8f75e3d643544d3e34acd18340dcf3f38acd17307cb0b284c8e3208c6d7170c4770d8c24f040bfd2fb6bde2f48bbf2ea9b992e2db76ad95b57ad0bb2fec88b162c1aaf56b89acdab06aaeaa6ea88a9cfa662961a4aa8f3a2f2885a13a8179f8278d9d067119b866b19a06651984e5dc967a56794a64e492b647690e24018f0e3858ce63028b1228d8922211871618e852611283520ab81b60287fc5fb37e0df457c39ed77a2de467859ddf76a1d6a74cdcf572f9c7970edbf66ee1b7a6cb9af76ae5a8268f5a06673d99865a192363b18bc621584e605d7e75ec17795d257125b1968f5929613577159e556551b537549f51bd4314fcd3a74d893244b992a849c523347d51b745ad14244110cd425905f4084ff13ee8f8a3d4cf153b24e993950e1d3760da135a8d41340cccc3238c573064be22eacb7b2d2cb142b58a982984a3128589d826a097f253c92623f48b8220484a20) else (if i < 3 then 0xd14a8c1096ac362c3a0b1aa8d9a0fb2361c5a0c142d5ab8c93161d14cd50695c64787168a6d2936d0d67cd8b0e8994d46988de1d130d506cd34cf9b161d1329366b3e6c5a2634a1a62299f31b358744cab11b35a2634988c74f19323c38b44c695b44f9934cc38b41ba6a348c693624f8744c375984e53166c33341ba5a674c9e661c5a0d5351a47369f126c3a261aacb474e51362c33341aaaa26c586668666a8a8533e6c58744ca33e6c58666898e9b34533e6c58744ca8dc74f19314c46b0e89959b359f362c3a0a4ca4da7cd8b0ccd13982242326c43d3e1d132b3660a66c49f0e89949ace9b16199a272c448474f88726c3a265668b474e53126c3a265498d62c3a26339f11699a1a1b18c10859b0e8986e8368f087cd8b44c69496a8d03c2c33341b3151b34403c24d866682c62bc462668686862c423a78d0b0e8986aa351d3a3c31b16898d2a3151a068586668345aa3668807851b0ccd060b56d159bc58741a9d21bc26b168693b4569f161d06a768ad362c3a0dced111bc3a161a9da6c378b0e835390d847161d05a721b08e2c3a0c4e4011bc3a161a9c88f1c2b667cd86a62d15cb8f1a21b3553161d1554cf9b0acd13443788d68a936136531683536c2d8b4143736c318b41435367cd88d9a29a1650ad3a6498b4149f1d4d99f361c5a28d810de2d050d4f2e3c68787168a942b4e99211c38b414a63ec2d8b0e8373d4971b161d06e7212f1c6c31f168a23ecc5853683738ad91f1612da0dd15036c378b0e82d4542410a6cc5863e83554b8d1f161d06e731b3347c58741ba25c6c38a3e8293d44db0a62c25b41ba5a2b4d8b0e83739b30d15a6491f161d15180e9311bd0d2736ad323c31f168694b4046f0ccd06a7699f31b358744ca0d9a99a1a4a451e1cf9a6686941a689d366c3a261ba5a27cd8744c373bbcd533bac3a2651873e629a264c9aa66769f0e899427c399d94d1327d906a1bc5a0d4e920e637b339ac45345498d6c4f9aa62d06e9d99b168286e68db0c62c3a0d4f525c7c58741a9c84bc71f0c6c5a288db31614fa0d4e1f606c584c682d454971b161d062737523c6cf8742c354c7699ed46c3a16511cdec8d9da62d06a915b2362c26341aa2a07d86b161d0628a848214d98b0c6d06ea971e362c3a0d4e5b6678d8b0e83544b8f87146d0527b41f646c388c682d49b971b161d0627a91b3e1d0b0d4f1b0e7b45342c9f667c5a0a1a9aa27d85316131a0d5243647c58741a9e362c3a299a99a6c8f8b0e8353908d8f0e2d14e7d84f1611fa0d4f1b0d3d0b0d4d6a334c2b34539e36c698a9e8353ecc5849e835334569f161d06a73459a2b4e92362c3a2a2c1926235a1a4e695a74786362d0d2968ad3e2c3a0b4e695a7c5874169c80f1d9f361d1328a91e31b358b0e8994e268533e6c3a26511e363298b0e899418a9193 else 0x6c4984de2d069a506ea6ccf98d14c5874552d5c4206f161d06a94f9b626c58741ba33a6d89f161d06a8366b3e6c58742ca25ab8e9e32686470e2d152c37b1247c5a0b34a25ab4c90d148d8a3e1d06ec232d5a64786347c5a1a566126ccd1f0e2d06ca546b6248d8b4186944b569d21b291f146c3a0d58465ab4e8f0c78d8b434aea340fb0362c3a0b1aa8b1096ac3e2c3a0c1ba8b24d99e361c5a))
def layer511r11 : Packing := (246,2,5,63,0,14,1,packed511r11)
def keys511k12 (i : Nat) : Nat := 0x826dc969005df5a9a0c6984e3644d46c8b8d57902f48b813b7f43c35a0f5d5ea5eb5b010f1d50b2cfc7093cee4c5e009afb8b177255000962a3ef56d41a79024d9e430a1a307542f6a1ead86fbd0004d09aac8daa85a22605ed97b0006288cc1a14e7c941911a06dfce000000051ba9be3df6b41c3c300080694f20c44cd219516d2000d7a12759c1c0e46572fd6cd36d4f71e9f031259a180000e8f162f0000a6176e08f000000754092ab08650007135e40005f4000000c95015b4021126d0004c2183b20a0e0b22808a41ef9230003105d100074ec5fc7f8cb5eb97eeab42f4e6d4adadcb950da370008b1f5e000032f7ccb6000a4b000cacf0435af882965d80001cd000aa600052ebae739e451bc43c0007bb000000bb490ae67b0953a0005980476f27e100032b6ca0000000000ece0b633ace6292de6e99c95e3617fc41da87493b0637a948989db8a83faddd5b673f5d07d297a26a688d9f4408e2785d7064887325c76e85938e66c58d700be51f249599b1d62d000aba812f757534221b361ed2aacf7f31db0006347e5803bbf619ac845286f4a3ce2c8c2084c1aa7714190d5c00071d0600004b002a040201040424000819070f09050007000c0000260009001b000231170214000000160002040326010002030975060200220e26050504002210230a1100010228040005008b01270000
def packed511r12 (i : Nat) : Nat := 0x51b9ac9da8a1a29114b279a2868a046ec9da8a85280e1b279a2a14a141ac9876e2868a54b261db8a1a28507b2719a8a1a2952c9c66a2868a066ac8a1a139d48a79a1a0c9d48a79a13289d41e29a16cca285068a785a328a2c9e68a1a268ec5279a18a8a2c9878a1a269e684ca255279a13289ac9e6522a26b271a286899c8a79943289e79a132896013cc72cd81922ee5649f12621c3d86d8c01562403d8690a80fc15012000ffe88ffd87ffc87ffe77ffd86ffd76ffd82ffd72ffd62ffd80ffd70ffd60ffd20bfe88dfe77efe66fbd84fbd74fdd83fee22fdd30ffa00
def layer511r12 : Packing := (22,1,5,63,0,11,1,packed511r12)
def keys511k13 (i : Nat) : Nat := 0xb40000000031000e00000000000012a00e3800000000002a600c8800000000000000000003a000000000000000000029a300000320000001c3a50000000000000000870000000ca0000000000000000000000000005b0000000000004510800000000002880047dac00000000000002103
def packed511r13 (i : Nat) : Nat := 0xc3984144dff
def layer511r13 : Packing := (1,0,5,63,0,0,1,packed511r13)
def samples511 : Array (Bits × Bits) := #[(0x900249000021870c30e4f90003fffc18301a130591b009a5000270003fff0c3cccc0f0fcccc0003333cccc000fffffff,0x550900249029400830400245902a902ac08100a1100909000a502aa302a80ab041cccc0505cccc14a1111cccc1525554153),(0x924000003338e0000c618332cb8ce0003000020486c1c0a024936c600039fffc00030c0f0fccccf0f0000ccccfffffffcccc000,0x925033003338e418c4208132cb8ce419b419800082c1400000912c6419a9419d0661040505ccccf0f10c6444455550c7cccd0ca),(0x442080000000000000318e1c3cf3f0ffffc0000c1818060cce38e38f80003e0000000c30f0f0f0f0ffffffff0f0f0f0000f0f0000,0x4420820f0000000083d08a141452d0b087c087840808020cce38e38f8107be107841e41050505050555441ff0f0f0f0436f0f043a),(0x88c30000ce3c3f00003e0fe03f03ff0000000030e0e0f80f0fc0fc0fffffc00000000fc0ff00ff00ff00000ff00ff00000ff00000,0x88c330ffce3c3f0c7bfe0fe03f03ff0c7f8c7f90a0a0e8050b40b40efc7fc0c7fb1fefc0ff00ff00ff033deff00ff033f6ff033fa),(0xffffffffffffffffffffffaf0fc0000f03fc000003ff0003ffc00000000003f00ff000ff000fff00000000000000fff0000ffff0000000ffff0000000fffffff,0xffffffffffffffffffffffaf0fc36aaf03fc00dd2bff0003ffc000dd50dd53f00ff000ff000fff00f5500f553d54fbe0000fafa0003e94eeee0003ea4aaabeac),(0xffffffffffffffffffffffcff000000ffc00000003fffffc00000000000003fff00000fffff00000000000000000fffffff00000000000fffffffffff0000000,0xffffffffffffffffffffffcff0026ccffc00009e33bdf7ec0000009e609e63fff00000fffff00000b6600b662d98efbfafa00000002f18bbbbaaaaf380002f30),(0xfffffffffffffffffffffff00000000ffffffffffc00000000000000000003ffffffff0000000000000000000000ffffffffffffffffff000000000000000000,0xfffffffffffffffffffffff000004f05b556db17c000000000000017801783bf7f7fdf00000000002780027809e0befafafafafaaa8be000000000bc00000bc0),(0xfffffffffffffffffffffffffffffff0000000000000000000000000000003ffffffffffffffffffffffffffffff000000000000000000000000000000000000,0xfffffffffffffffffffffff552487000000000180000000000000018001802f5e5d16aaf4b64ad10380143800e00000000000000000c0000000000c000000c00),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000000000000000000000000000000,0xaadb7800a4aa924e002f75cbabad2a4e002e000000000000000000000c0000c003000000000000000003000000000030000003000)]
def cols511 : IndexTree ColumnInfo := (.fork 15 (.fork 7 (.fork 3 (.leaf [(0,32,477,2,12),(8,0,503,0,12),(16,0,495,0,12)]) (.leaf [(32,0,479,0,12),(0,16,494,1,11),(2,0,477,0,11),(4,0,507,0,11)])) (.fork 4 (.leaf [(64,0,447,0,11),(2,32,477,0,11),(24,0,487,0,11),(0,8,375,128,10)]) (.leaf [(1,0,494,0,10),(1,16,494,0,10),(0,2,341,160,9),(0,4,187,320,9)]))) (.fork 7 (.fork 3 (.leaf [(0,64,187,260,9),(128,0,375,0,9),(256,0,255,0,9)]) (.leaf [(8,2,341,160,9),(68,0,443,0,9),(128,8,375,0,9),(136,0,375,0,9)])) (.fork 4 (.leaf [(4,64,187,256,8),(9,0,486,0,8),(64,4,187,256,8),(128,2,341,32,8)]) (.leaf [(256,4,187,64,8),(256,64,187,4,8),(9,16,486,0,8),(136,2,341,32,8)]))))
def levels511 : Nat → Packing
  | 6 => layer511r6
  | 7 => layer511r7
  | 8 => layer511r8
  | 9 => layer511r9
  | 10 => layer511r10
  | 11 => layer511r11
  | 12 => layer511r12
  | 13 => layer511r13
  | _ => emptyPacking
def index511 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 3 0 5 1 0 keys511k7
  | 8 => lookupWord 16 59 6 10 6 0 keys511k8
  | 9 => lookupWord 104 354 7 13 9 0 keys511k9
  | 10 => lookupWord 295 1003 8 14 10 0 keys511k10
  | 11 => lookupWord 330 1121 8 14 10 0 keys511k11
  | 12 => lookupWord 82 281 8 12 8 0 keys511k12
  | 13 => lookupWord 7 101 1 9 5 0 keys511k13
  | _ => fun _ => none
def g511 : Forest := ⟨511,13,fun j => samples511[j]?.getD (0,0),cols511,#[[]],levels511,index511,noFactory,noFactorySound 511⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom324 : graphValid g324 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice324k3p0 : block g324 3 0 1 = true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK324k3 : block g324 3 0 1=true := slice324k3p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked324 : checkedTables g324 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g324 0 0 0=true)
  · exact (rfl : block g324 1 0 0=true)
  · exact (rfl : block g324 2 0 0=true)
  · exact layerOK324k3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low324 : Lower (vars 324) (graphGoal 324) 4 :=
  lower_forest (g:=g324) (i:=0) (hints:=8623490560) (before_sound [] baseKnown) geom324 checked324 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps324 : List (Nat × List Nat) := [(324,[]),(385,[118,16,32])]
def known324 := extendKnown [] 4 maps324
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid324 : Known known324 := extendKnown_ok baseKnown low324 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom147 : graphValid g147 (boundsBefore known324) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice147k3p0 : block g147 3 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK147k3 : block g147 3 0 1=true := slice147k3p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked147 : checkedTables g147 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g147 0 0 0=true)
  · exact (rfl : block g147 1 0 0=true)
  · exact (rfl : block g147 2 0 0=true)
  · exact layerOK147k3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low147 : Lower (vars 147) (graphGoal 147) 4 :=
  lower_forest (g:=g147) (i:=0) (hints:=116) (before_sound known324 valid324) geom147 checked147 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps147 : List (Nat × List Nat) := [(147,[]),(153,[49,33]),(163,[84,16]),(170,[84,49,16,32]),(277,[135,33]),(337,[135,97,81,49,33]),(390,[128,96,80,64,32])]
def known147 := extendKnown known324 4 maps147
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid147 : Known known147 := extendKnown_ok valid324 low147 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom325 : graphValid g325 (boundsBefore known147) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice325k4p0 : block g325 4 0 1 = true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK325k4 : block g325 4 0 1=true := slice325k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked325 : checkedTables g325 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g325 0 0 0=true)
  · exact (rfl : block g325 1 0 0=true)
  · exact (rfl : block g325 2 0 0=true)
  · exact (rfl : block g325 3 0 0=true)
  · exact layerOK325k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low325 : Lower (vars 325) (graphGoal 325) 5 :=
  lower_forest (g:=g325) (i:=0) (hints:=33555976) (before_sound known147 valid147) geom325 checked325 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps325 : List (Nat × List Nat) := [(325,[]),(389,[118,32]),(449,[96,112,80,64,48,32]),(452,[112,80,64,48,16])]
def known325 := extendKnown known147 5 maps325
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid325 : Known known325 := extendKnown_ok valid147 low325 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom358 : graphValid g358 (boundsBefore known325) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice358k5p0 : block g358 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK358k5 : block g358 5 0 1=true := slice358k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked358 : checkedTables g358 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g358 0 0 0=true)
  · exact (rfl : block g358 1 0 0=true)
  · exact (rfl : block g358 2 0 0=true)
  · exact (rfl : block g358 3 0 0=true)
  · exact (rfl : block g358 4 0 0=true)
  · exact layerOK358k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low358 : Lower (vars 358) (graphGoal 358) 6 :=
  lower_forest (g:=g358) (i:=0) (hints:=8624539216) (before_sound known325 valid325) geom358 checked358 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps358 : List (Nat × List Nat) := [(358,[])]
def known358 := extendKnown known325 6 maps358
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid358 : Known known358 := extendKnown_ok valid325 low358 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom179 : graphValid g179 (boundsBefore known358) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice179k4p0 : block g179 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK179k4 : block g179 4 0 1=true := slice179k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked179 : checkedTables g179 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0=true)
  · exact (rfl : block g179 1 0 0=true)
  · exact (rfl : block g179 2 0 0=true)
  · exact (rfl : block g179 3 0 0=true)
  · exact layerOK179k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low179 : Lower (vars 179) (graphGoal 179) 5 :=
  lower_forest (g:=g179) (i:=0) (hints:=1048660) (before_sound known358 valid358) geom179 checked179 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps179 : List (Nat × List Nat) := [(179,[]),(422,[129,65,100,81,16,32]),(482,[81,84,132,97,49,16,32])]
def known179 := extendKnown known358 5 maps179
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid179 : Known known179 := extendKnown_ok valid358 low179 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom155 : graphValid g155 (boundsBefore known179) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice155k4p0 : block g155 4 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK155k4 : block g155 4 0 1=true := slice155k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked155 : checkedTables g155 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g155 0 0 0=true)
  · exact (rfl : block g155 1 0 0=true)
  · exact (rfl : block g155 2 0 0=true)
  · exact (rfl : block g155 3 0 0=true)
  · exact layerOK155k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low155 : Lower (vars 155) (graphGoal 155) 5 :=
  lower_forest (g:=g155) (i:=0) (hints:=28788) (before_sound known179 valid179) geom155 checked155 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps155 : List (Nat × List Nat) := [(171,[84,16]),(426,[131,67,100,49,81,16,32])]
def known155 := extendKnown known179 5 maps155
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid155 : Known known155 := extendKnown_ok valid179 low155 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom341 : graphValid g341 (boundsBefore known155) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice341k5p0 : block g341 5 0 3 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice341k5p3 : block g341 5 3 4 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK341k5 : block g341 5 0 7=true := (@block_merge g341 5 0 3 4 slice341k5p0 slice341k5p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice341k6p0 : block g341 6 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK341k6 : block g341 6 0 1=true := slice341k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked341 : checkedTables g341 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g341 0 0 0=true)
  · exact (rfl : block g341 1 0 0=true)
  · exact (rfl : block g341 2 0 0=true)
  · exact (rfl : block g341 3 0 0=true)
  · exact (rfl : block g341 4 0 0=true)
  · exact layerOK341k5
  · exact layerOK341k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low341 : Lower (vars 341) (graphGoal 341) 7 :=
  lower_forest (g:=g341) (i:=0) (hints:=33555972) (before_sound known155 valid155) geom341 checked341 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps341 : List (Nat × List Nat) := [(341,[]),(419,[134,118,84,16,32]),(454,[112,80,64,16]),(460,[112,80,64,48,16])]
def known341 := extendKnown known155 7 maps341
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid341 : Known known341 := extendKnown_ok valid155 low341 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom391 : graphValid g391 (boundsBefore known341) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice391k5p0 : block g391 5 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK391k5 : block g391 5 0 1=true := slice391k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked391 : checkedTables g391 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g391 0 0 0=true)
  · exact (rfl : block g391 1 0 0=true)
  · exact (rfl : block g391 2 0 0=true)
  · exact (rfl : block g391 3 0 0=true)
  · exact (rfl : block g391 4 0 0=true)
  · exact layerOK391k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low391 : Lower (vars 391) (graphGoal 391) 6 :=
  lower_forest (g:=g391) (i:=0) (hints:=2167) (before_sound known341 valid341) geom391 checked391 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps391 : List (Nat × List Nat) := [(391,[]),(403,[128,65,49,33,112]),(405,[65,49,112])]
def known391 := extendKnown known341 6 maps391
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid391 : Known known391 := extendKnown_ok valid341 low391 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom453 : graphValid g453 (boundsBefore known391) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice453k4p0 : block g453 4 0 12 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK453k4 : block g453 4 0 12=true := slice453k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice453k5p0 : block g453 5 0 8 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice453k5p8 : block g453 5 8 29 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK453k5 : block g453 5 0 37=true := (@block_merge g453 5 0 8 29 slice453k5p0 slice453k5p8)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice453k6p0 : block g453 6 0 5 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice453k6p5 : block g453 6 5 9 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK453k6 : block g453 6 0 14=true := (@block_merge g453 6 0 5 9 slice453k6p0 slice453k6p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice453k7p0 : block g453 7 0 1 = true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK453k7 : block g453 7 0 1=true := slice453k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked453 : checkedTables g453 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g453 0 0 0=true)
  · exact (rfl : block g453 1 0 0=true)
  · exact (rfl : block g453 2 0 0=true)
  · exact (rfl : block g453 3 0 0=true)
  · exact layerOK453k4
  · exact layerOK453k5
  · exact layerOK453k6
  · exact layerOK453k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low453 : Lower (vars 453) (graphGoal 453) 8 :=
  lower_forest (g:=g453) (i:=0) (hints:=33555975) (before_sound known391 valid391) geom453 checked453 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps453 : List (Nat × List Nat) := [(453,[])]
def known453 := extendKnown known391 8 maps453
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid453 : Known known453 := extendKnown_ok valid391 low453 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom215 : graphValid g215 (boundsBefore known453) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice215k5p0 : block g215 5 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK215k5 : block g215 5 0 1=true := slice215k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked215 : checkedTables g215 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g215 0 0 0=true)
  · exact (rfl : block g215 1 0 0=true)
  · exact (rfl : block g215 2 0 0=true)
  · exact (rfl : block g215 3 0 0=true)
  · exact (rfl : block g215 4 0 0=true)
  · exact layerOK215k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low215 : Lower (vars 215) (graphGoal 215) 6 :=
  lower_forest (g:=g215) (i:=0) (hints:=33556084) (before_sound known453 valid453) geom215 checked215 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps215 : List (Nat × List Nat) := [(215,[]),(231,[84,16]),(238,[84,16,48]),(311,[135,101,33])]
def known215 := extendKnown known453 6 maps215
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid215 : Known known215 := extendKnown_ok valid453 low215 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom359 : graphValid g359 (boundsBefore known215) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice359k6p0 : block g359 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK359k6 : block g359 6 0 1=true := slice359k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked359 : checkedTables g359 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g359 0 0 0=true)
  · exact (rfl : block g359 1 0 0=true)
  · exact (rfl : block g359 2 0 0=true)
  · exact (rfl : block g359 3 0 0=true)
  · exact (rfl : block g359 4 0 0=true)
  · exact (rfl : block g359 5 0 0=true)
  · exact layerOK359k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low359 : Lower (vars 359) (graphGoal 359) 7 :=
  lower_forest (g:=g359) (i:=0) (hints:=34604632) (before_sound known215 valid215) geom359 checked359 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps359 : List (Nat × List Nat) := [(359,[])]
def known359 := extendKnown known215 7 maps359
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid359 : Known known359 := extendKnown_ok valid215 low359 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom187 : graphValid g187 (boundsBefore known359) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice187k6p0 : block g187 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK187k6 : block g187 6 0 1=true := slice187k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked187 : checkedTables g187 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0=true)
  · exact (rfl : block g187 1 0 0=true)
  · exact (rfl : block g187 2 0 0=true)
  · exact (rfl : block g187 3 0 0=true)
  · exact (rfl : block g187 4 0 0=true)
  · exact (rfl : block g187 5 0 0=true)
  · exact layerOK187k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low187 : Lower (vars 187) (graphGoal 187) 7 :=
  lower_forest (g:=g187) (i:=0) (hints:=1077332) (before_sound known359 valid359) geom187 checked187 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps187 : List (Nat × List Nat) := [(187,[]),(430,[129,65,100,81,16,32]),(490,[81,84,132,97,16,32])]
def known187 := extendKnown known359 7 maps187
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid187 : Known known187 := extendKnown_ok valid359 low187 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom486 : graphValid g486 (boundsBefore known187) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice486k7p0 : block g486 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK486k7 : block g486 7 0 1=true := slice486k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked486 : checkedTables g486 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g486 0 0 0=true)
  · exact (rfl : block g486 1 0 0=true)
  · exact (rfl : block g486 2 0 0=true)
  · exact (rfl : block g486 3 0 0=true)
  · exact (rfl : block g486 4 0 0=true)
  · exact (rfl : block g486 5 0 0=true)
  · exact (rfl : block g486 6 0 0=true)
  · exact layerOK486k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low486 : Lower (vars 486) (graphGoal 486) 8 :=
  lower_forest (g:=g486) (i:=0) (hints:=8892974672) (before_sound known187 valid187) geom486 checked486 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps486 : List (Nat × List Nat) := [(486,[])]
def known486 := extendKnown known187 8 maps486
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid486 : Known known486 := extendKnown_ok valid187 low486 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom423 : graphValid g423 (boundsBefore known486) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice423k7p0 : block g423 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK423k7 : block g423 7 0 1=true := slice423k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked423 : checkedTables g423 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g423 0 0 0=true)
  · exact (rfl : block g423 1 0 0=true)
  · exact (rfl : block g423 2 0 0=true)
  · exact (rfl : block g423 3 0 0=true)
  · exact (rfl : block g423 4 0 0=true)
  · exact (rfl : block g423 5 0 0=true)
  · exact (rfl : block g423 6 0 0=true)
  · exact layerOK423k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low423 : Lower (vars 423) (graphGoal 423) 8 :=
  lower_forest (g:=g423) (i:=0) (hints:=1050711) (before_sound known486 valid486) geom423 checked423 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps423 : List (Nat × List Nat) := [(423,[]),(435,[66,50,128]),(483,[98,66,50])]
def known423 := extendKnown known486 8 maps423
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid423 : Known known423 := extendKnown_ok valid486 low423 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom427 : graphValid g427 (boundsBefore known423) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice427k7p0 : block g427 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK427k7 : block g427 7 0 1=true := slice427k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked427 : checkedTables g427 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g427 0 0 0=true)
  · exact (rfl : block g427 1 0 0=true)
  · exact (rfl : block g427 2 0 0=true)
  · exact (rfl : block g427 3 0 0=true)
  · exact (rfl : block g427 4 0 0=true)
  · exact (rfl : block g427 5 0 0=true)
  · exact (rfl : block g427 6 0 0=true)
  · exact layerOK427k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low427 : Lower (vars 427) (graphGoal 427) 8 :=
  lower_forest (g:=g427) (i:=0) (hints:=1077335) (before_sound known423 valid423) geom427 checked427 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps427 : List (Nat × List Nat) := [(427,[])]
def known427 := extendKnown known423 8 maps427
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid427 : Known known427 := extendKnown_ok valid423 low427 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom407 : graphValid g407 (boundsBefore known427) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice407k6p0 : block g407 6 0 9 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice407k6p9 : block g407 6 9 3 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK407k6 : block g407 6 0 12=true := (@block_merge g407 6 0 9 3 slice407k6p0 slice407k6p9)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice407k7p0 : block g407 7 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK407k7 : block g407 7 0 1=true := slice407k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked407 : checkedTables g407 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g407 0 0 0=true)
  · exact (rfl : block g407 1 0 0=true)
  · exact (rfl : block g407 2 0 0=true)
  · exact (rfl : block g407 3 0 0=true)
  · exact (rfl : block g407 4 0 0=true)
  · exact (rfl : block g407 5 0 0=true)
  · exact layerOK407k6
  · exact layerOK407k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low407 : Lower (vars 407) (graphGoal 407) 8 :=
  lower_forest (g:=g407) (i:=0) (hints:=2164) (before_sound known427 valid427) geom407 checked407 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps407 : List (Nat × List Nat) := [(407,[]),(413,[135,33,49]),(467,[98,82,50])]
def known407 := extendKnown known427 8 maps407
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid407 : Known known407 := extendKnown_ok valid427 low407 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom455 : graphValid g455 (boundsBefore known407) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice455k8p0 : block g455 8 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK455k8 : block g455 8 0 1=true := slice455k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked455 : checkedTables g455 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g455 0 0 0=true)
  · exact (rfl : block g455 1 0 0=true)
  · exact (rfl : block g455 2 0 0=true)
  · exact (rfl : block g455 3 0 0=true)
  · exact (rfl : block g455 4 0 0=true)
  · exact (rfl : block g455 5 0 0=true)
  · exact (rfl : block g455 6 0 0=true)
  · exact (rfl : block g455 7 0 0=true)
  · exact layerOK455k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low455 : Lower (vars 455) (graphGoal 455) 9 :=
  lower_forest (g:=g455) (i:=0) (hints:=33556087) (before_sound known407 valid407) geom455 checked455 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps455 : List (Nat × List Nat) := [(455,[]),(469,[65,49,112])]
def known455 := extendKnown known407 9 maps455
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid455 : Known known455 := extendKnown_ok valid407 low455 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom375 : graphValid g375 (boundsBefore known455) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice375k8p0 : block g375 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK375k8 : block g375 8 0 1=true := slice375k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked375 : checkedTables g375 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g375 0 0 0=true)
  · exact (rfl : block g375 1 0 0=true)
  · exact (rfl : block g375 2 0 0=true)
  · exact (rfl : block g375 3 0 0=true)
  · exact (rfl : block g375 4 0 0=true)
  · exact (rfl : block g375 5 0 0=true)
  · exact (rfl : block g375 6 0 0=true)
  · exact (rfl : block g375 7 0 0=true)
  · exact layerOK375k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low375 : Lower (vars 375) (graphGoal 375) 9 :=
  lower_forest (g:=g375) (i:=0) (hints:=34604628) (before_sound known455 valid455) geom375 checked375 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps375 : List (Nat × List Nat) := [(375,[])]
def known375 := extendKnown known455 9 maps375
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid375 : Known known375 := extendKnown_ok valid455 low375 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom494 : graphValid g494 (boundsBefore known375) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=2) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k7p0 : block g494 7 0 9 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k7p9 : block g494 7 9 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK494k7 : block g494 7 0 10=true := (@block_merge g494 7 0 9 1 slice494k7p0 slice494k7p9)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k8p0 : block g494 8 0 5 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k8p5 : block g494 8 5 7 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK494k8 : block g494 8 0 12=true := (@block_merge g494 8 0 5 7 slice494k8p0 slice494k8p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice494k9p0 : block g494 9 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK494k9 : block g494 9 0 1=true := slice494k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked494 : checkedTables g494 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g494 0 0 0=true)
  · exact (rfl : block g494 1 0 0=true)
  · exact (rfl : block g494 2 0 0=true)
  · exact (rfl : block g494 3 0 0=true)
  · exact (rfl : block g494 4 0 0=true)
  · exact (rfl : block g494 5 0 0=true)
  · exact (rfl : block g494 6 0 0=true)
  · exact layerOK494k7
  · exact layerOK494k8
  · exact layerOK494k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low494 : Lower (vars 494) (graphGoal 494) 10 :=
  lower_forest (g:=g494) (i:=0) (hints:=8893003344) (before_sound known375 valid375) geom494 checked494 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps494 : List (Nat × List Nat) := [(494,[])]
def known494 := extendKnown known375 10 maps494
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid494 : Known known494 := extendKnown_ok valid375 low494 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom439 : graphValid g439 (boundsBefore known494) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice439k8p0 : block g439 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK439k8 : block g439 8 0 1=true := slice439k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked439 : checkedTables g439 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g439 0 0 0=true)
  · exact (rfl : block g439 1 0 0=true)
  · exact (rfl : block g439 2 0 0=true)
  · exact (rfl : block g439 3 0 0=true)
  · exact (rfl : block g439 4 0 0=true)
  · exact (rfl : block g439 5 0 0=true)
  · exact (rfl : block g439 6 0 0=true)
  · exact (rfl : block g439 7 0 0=true)
  · exact layerOK439k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low439 : Lower (vars 439) (graphGoal 439) 9 :=
  lower_forest (g:=g439) (i:=0) (hints:=1050708) (before_sound known494 valid494) geom439 checked439 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps439 : List (Nat × List Nat) := [(439,[])]
def known439 := extendKnown known494 9 maps439
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid439 : Known known439 := extendKnown_ok valid494 low439 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom431 : graphValid g431 (boundsBefore known439) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice431k8p0 : block g431 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK431k8 : block g431 8 0 1=true := slice431k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked431 : checkedTables g431 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g431 0 0 0=true)
  · exact (rfl : block g431 1 0 0=true)
  · exact (rfl : block g431 2 0 0=true)
  · exact (rfl : block g431 3 0 0=true)
  · exact (rfl : block g431 4 0 0=true)
  · exact (rfl : block g431 5 0 0=true)
  · exact (rfl : block g431 6 0 0=true)
  · exact (rfl : block g431 7 0 0=true)
  · exact layerOK431k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low431 : Lower (vars 431) (graphGoal 431) 9 :=
  lower_forest (g:=g431) (i:=0) (hints:=1079383) (before_sound known439 valid439) geom431 checked431 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps431 : List (Nat × List Nat) := [(431,[]),(443,[66,128])]
def known431 := extendKnown known439 9 maps431
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid431 : Known known431 := extendKnown_ok valid439 low431 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom415 : graphValid g415 (boundsBefore known431) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice415k8p0 : block g415 8 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK415k8 : block g415 8 0 1=true := slice415k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked415 : checkedTables g415 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g415 0 0 0=true)
  · exact (rfl : block g415 1 0 0=true)
  · exact (rfl : block g415 2 0 0=true)
  · exact (rfl : block g415 3 0 0=true)
  · exact (rfl : block g415 4 0 0=true)
  · exact (rfl : block g415 5 0 0=true)
  · exact (rfl : block g415 6 0 0=true)
  · exact (rfl : block g415 7 0 0=true)
  · exact layerOK415k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low415 : Lower (vars 415) (graphGoal 415) 9 :=
  lower_forest (g:=g415) (i:=0) (hints:=30836) (before_sound known431 valid431) geom415 checked415 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps415 : List (Nat × List Nat) := [(415,[])]
def known415 := extendKnown known431 9 maps415
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid415 : Known known415 := extendKnown_ok valid431 low415 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom487 : graphValid g487 (boundsBefore known415) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k6p0 : block g487 6 0 6 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k6p6 : block g487 6 6 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK487k6 : block g487 6 0 7=true := (@block_merge g487 6 0 6 1 slice487k6p0 slice487k6p6)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k7p0 : block g487 7 0 42 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k7p42 : block g487 7 42 30 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK487k7 : block g487 7 0 72=true := (@block_merge g487 7 0 42 30 slice487k7p0 slice487k7p42)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k8p0 : block g487 8 0 13 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k8p13 : block g487 8 13 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k8p77 : block g487 8 77 21 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k8p98 : block g487 8 98 30 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK487k8 : block g487 8 0 128=true := (@block_merge g487 8 0 98 30 (@block_merge g487 8 0 77 21 (@block_merge g487 8 0 13 64 slice487k8p0 slice487k8p13) slice487k8p77) slice487k8p98)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k9p0 : block g487 9 0 5 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k9p5 : block g487 9 5 12 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK487k9 : block g487 9 0 17=true := (@block_merge g487 9 0 5 12 slice487k9p0 slice487k9p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice487k10p0 : block g487 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK487k10 : block g487 10 0 1=true := slice487k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked487 : checkedTables g487 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g487 0 0 0=true)
  · exact (rfl : block g487 1 0 0=true)
  · exact (rfl : block g487 2 0 0=true)
  · exact (rfl : block g487 3 0 0=true)
  · exact (rfl : block g487 4 0 0=true)
  · exact (rfl : block g487 5 0 0=true)
  · exact layerOK487k6
  · exact layerOK487k7
  · exact layerOK487k8
  · exact layerOK487k9
  · exact layerOK487k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low487 : Lower (vars 487) (graphGoal 487) 11 :=
  lower_forest (g:=g487) (i:=0) (hints:=34604631) (before_sound known415 valid415) geom487 checked487 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps487 : List (Nat × List Nat) := [(487,[])]
def known487 := extendKnown known415 11 maps487
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid487 : Known known487 := extendKnown_ok valid415 low487 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom471 : graphValid g471 (boundsBefore known487) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice471k6p0 : block g471 6 0 8 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice471k6p8 : block g471 6 8 16 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK471k6 : block g471 6 0 24=true := (@block_merge g471 6 0 8 16 slice471k6p0 slice471k6p8)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice471k7p0 : block g471 7 0 61 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice471k7p61 : block g471 7 61 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice471k7p125 : block g471 7 125 10 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK471k7 : block g471 7 0 135=true := (@block_merge g471 7 0 125 10 (@block_merge g471 7 0 61 64 slice471k7p0 slice471k7p61) slice471k7p125)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice471k8p0 : block g471 8 0 25 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice471k8p25 : block g471 8 25 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice471k8p89 : block g471 8 89 50 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice471k8p139 : block g471 8 139 37 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK471k8 : block g471 8 0 176=true := (@block_merge g471 8 0 139 37 (@block_merge g471 8 0 89 50 (@block_merge g471 8 0 25 64 slice471k8p0 slice471k8p25) slice471k8p89) slice471k8p139)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice471k9p0 : block g471 9 0 9 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice471k9p9 : block g471 9 9 11 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK471k9 : block g471 9 0 20=true := (@block_merge g471 9 0 9 11 slice471k9p0 slice471k9p9)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice471k10p0 : block g471 10 0 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK471k10 : block g471 10 0 1=true := slice471k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked471 : checkedTables g471 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g471 0 0 0=true)
  · exact (rfl : block g471 1 0 0=true)
  · exact (rfl : block g471 2 0 0=true)
  · exact (rfl : block g471 3 0 0=true)
  · exact (rfl : block g471 4 0 0=true)
  · exact (rfl : block g471 5 0 0=true)
  · exact layerOK471k6
  · exact layerOK471k7
  · exact layerOK471k8
  · exact layerOK471k9
  · exact layerOK471k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low471 : Lower (vars 471) (graphGoal 471) 11 :=
  lower_forest (g:=g471) (i:=0) (hints:=33556084) (before_sound known487 valid487) geom471 checked471 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps471 : List (Nat × List Nat) := [(477,[49])]
def known471 := extendKnown known487 11 maps471
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid471 : Known known471 := extendKnown_ok valid487 low471 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom255 : graphValid g255 (boundsBefore known471) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice255k8p0 : block g255 8 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK255k8 : block g255 8 0 1=true := slice255k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked255 : checkedTables g255 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0=true)
  · exact (rfl : block g255 1 0 0=true)
  · exact (rfl : block g255 2 0 0=true)
  · exact (rfl : block g255 3 0 0=true)
  · exact (rfl : block g255 4 0 0=true)
  · exact (rfl : block g255 5 0 0=true)
  · exact (rfl : block g255 6 0 0=true)
  · exact (rfl : block g255 7 0 0=true)
  · exact layerOK255k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 9 :=
  lower_forest (g:=g255) (i:=0) (hints:=34633300) (before_sound known471 valid471) geom255 checked255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps255 : List (Nat × List Nat) := [(255,[])]
def known255 := extendKnown known471 9 maps255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known known255 := extendKnown_ok valid471 low255 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom447 : graphValid g447 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice447k6p0 : block g447 6 0 2 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice447k6p2 : block g447 6 2 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK447k6 : block g447 6 0 4=true := (@block_merge g447 6 0 2 2 slice447k6p0 slice447k6p2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice447k7p0 : block g447 7 0 6 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice447k7p6 : block g447 7 6 11 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK447k7 : block g447 7 0 17=true := (@block_merge g447 7 0 6 11 slice447k7p0 slice447k7p6)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice447k8p0 : block g447 8 0 25 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice447k8p25 : block g447 8 25 16 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK447k8 : block g447 8 0 41=true := (@block_merge g447 8 0 25 16 slice447k8p0 slice447k8p25)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice447k9p0 : block g447 9 0 9 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice447k9p9 : block g447 9 9 4 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK447k9 : block g447 9 0 13=true := (@block_merge g447 9 0 9 4 slice447k9p0 slice447k9p9)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice447k10p0 : block g447 10 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK447k10 : block g447 10 0 1=true := slice447k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked447 : checkedTables g447 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g447 0 0 0=true)
  · exact (rfl : block g447 1 0 0=true)
  · exact (rfl : block g447 2 0 0=true)
  · exact (rfl : block g447 3 0 0=true)
  · exact (rfl : block g447 4 0 0=true)
  · exact (rfl : block g447 5 0 0=true)
  · exact layerOK447k6
  · exact layerOK447k7
  · exact layerOK447k8
  · exact layerOK447k9
  · exact layerOK447k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low447 : Lower (vars 447) (graphGoal 447) 11 :=
  lower_forest (g:=g447) (i:=0) (hints:=1079380) (before_sound known255 valid255) geom447 checked447 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps447 : List (Nat × List Nat) := [(447,[]),(507,[98])]
def known447 := extendKnown known255 11 maps447
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid447 : Known known447 := extendKnown_ok valid255 low447 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom503 : graphValid g503 (boundsBefore known447) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice503k11p0 : block g503 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK503k11 : block g503 11 0 1=true := slice503k11p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked503 : checkedTables g503 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g503 0 0 0=true)
  · exact (rfl : block g503 1 0 0=true)
  · exact (rfl : block g503 2 0 0=true)
  · exact (rfl : block g503 3 0 0=true)
  · exact (rfl : block g503 4 0 0=true)
  · exact (rfl : block g503 5 0 0=true)
  · exact (rfl : block g503 6 0 0=true)
  · exact (rfl : block g503 7 0 0=true)
  · exact (rfl : block g503 8 0 0=true)
  · exact (rfl : block g503 9 0 0=true)
  · exact (rfl : block g503 10 0 0=true)
  · exact layerOK503k11
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low503 : Lower (vars 503) (graphGoal 503) 12 :=
  lower_forest (g:=g503) (i:=0) (hints:=34604628) (before_sound known447 valid447) geom503 checked503 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps503 : List (Nat × List Nat) := [(503,[])]
def known503 := extendKnown known447 12 maps503
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid503 : Known known503 := extendKnown_ok valid447 low503 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom495 : graphValid g495 (boundsBefore known503) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice495k11p0 : block g495 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK495k11 : block g495 11 0 1=true := slice495k11p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked495 : checkedTables g495 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g495 0 0 0=true)
  · exact (rfl : block g495 1 0 0=true)
  · exact (rfl : block g495 2 0 0=true)
  · exact (rfl : block g495 3 0 0=true)
  · exact (rfl : block g495 4 0 0=true)
  · exact (rfl : block g495 5 0 0=true)
  · exact (rfl : block g495 6 0 0=true)
  · exact (rfl : block g495 7 0 0=true)
  · exact (rfl : block g495 8 0 0=true)
  · exact (rfl : block g495 9 0 0=true)
  · exact (rfl : block g495 10 0 0=true)
  · exact layerOK495k11
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low495 : Lower (vars 495) (graphGoal 495) 12 :=
  lower_forest (g:=g495) (i:=0) (hints:=34633303) (before_sound known503 valid503) geom495 checked495 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps495 : List (Nat × List Nat) := [(495,[])]
def known495 := extendKnown known503 12 maps495
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid495 : Known known495 := extendKnown_ok valid503 low495 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom479 : graphValid g479 (boundsBefore known495) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice479k11p0 : block g479 11 0 1 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK479k11 : block g479 11 0 1=true := slice479k11p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked479 : checkedTables g479 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g479 0 0 0=true)
  · exact (rfl : block g479 1 0 0=true)
  · exact (rfl : block g479 2 0 0=true)
  · exact (rfl : block g479 3 0 0=true)
  · exact (rfl : block g479 4 0 0=true)
  · exact (rfl : block g479 5 0 0=true)
  · exact (rfl : block g479 6 0 0=true)
  · exact (rfl : block g479 7 0 0=true)
  · exact (rfl : block g479 8 0 0=true)
  · exact (rfl : block g479 9 0 0=true)
  · exact (rfl : block g479 10 0 0=true)
  · exact layerOK479k11
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low479 : Lower (vars 479) (graphGoal 479) 12 :=
  lower_forest (g:=g479) (i:=0) (hints:=33584756) (before_sound known495 valid495) geom479 checked479 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps479 : List (Nat × List Nat) := [(479,[])]
def known479 := extendKnown known495 12 maps479
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid479 : Known known479 := extendKnown_ok valid495 low479 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem geom511 : graphValid g511 (boundsBefore known479) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k6p0 : block g511 6 0 1 = true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k6p1 : block g511 6 1 1 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k6 : block g511 6 0 2=true := (@block_merge g511 6 0 1 1 slice511k6p0 slice511k6p1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k7p0 : block g511 7 0 36 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k7p36 : block g511 7 36 13 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k7 : block g511 7 0 49=true := (@block_merge g511 7 0 36 13 slice511k7p0 slice511k7p36)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k8p0 : block g511 8 0 10 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k8p10 : block g511 8 10 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k8p74 : block g511 8 74 64 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k8p138 : block g511 8 138 47 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k8p185 : block g511 8 185 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k8p249 : block g511 8 249 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k8 : block g511 8 0 313=true := (@block_merge g511 8 0 249 64 (@block_merge g511 8 0 185 64 (@block_merge g511 8 0 138 47 (@block_merge g511 8 0 74 64 (@block_merge g511 8 0 10 64 slice511k8p0 slice511k8p10) slice511k8p74) slice511k8p138) slice511k8p185) slice511k8p249)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p0 : block g511 9 0 2 = true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p2 : block g511 9 2 48 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p50 : block g511 9 50 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p114 : block g511 9 114 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p178 : block g511 9 178 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p242 : block g511 9 242 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p306 : block g511 9 306 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p370 : block g511 9 370 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p434 : block g511 9 434 7 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p441 : block g511 9 441 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p505 : block g511 9 505 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p569 : block g511 9 569 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p633 : block g511 9 633 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p697 : block g511 9 697 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p761 : block g511 9 761 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k9p825 : block g511 9 825 62 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k9 : block g511 9 0 887=true := (@block_merge g511 9 0 825 62 (@block_merge g511 9 0 761 64 (@block_merge g511 9 0 697 64 (@block_merge g511 9 0 633 64 (@block_merge g511 9 0 569 64 (@block_merge g511 9 0 505 64 (@block_merge g511 9 0 441 64 (@block_merge g511 9 0 434 7 (@block_merge g511 9 0 370 64 (@block_merge g511 9 0 306 64 (@block_merge g511 9 0 242 64 (@block_merge g511 9 0 178 64 (@block_merge g511 9 0 114 64 (@block_merge g511 9 0 50 64 (@block_merge g511 9 0 2 48 slice511k9p0 slice511k9p2) slice511k9p50) slice511k9p114) slice511k9p178) slice511k9p242) slice511k9p306) slice511k9p370) slice511k9p434) slice511k9p441) slice511k9p505) slice511k9p569) slice511k9p633) slice511k9p697) slice511k9p761) slice511k9p825)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p0 : block g511 10 0 7 = true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p7 : block g511 10 7 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p71 : block g511 10 71 64 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p135 : block g511 10 135 35 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p170 : block g511 10 170 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p234 : block g511 10 234 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p298 : block g511 10 298 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p362 : block g511 10 362 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p426 : block g511 10 426 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p490 : block g511 10 490 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p554 : block g511 10 554 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p618 : block g511 10 618 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p682 : block g511 10 682 19 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p701 : block g511 10 701 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p765 : block g511 10 765 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p829 : block g511 10 829 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p893 : block g511 10 893 64 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k10p957 : block g511 10 957 34 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k10 : block g511 10 0 991=true := (@block_merge g511 10 0 957 34 (@block_merge g511 10 0 893 64 (@block_merge g511 10 0 829 64 (@block_merge g511 10 0 765 64 (@block_merge g511 10 0 701 64 (@block_merge g511 10 0 682 19 (@block_merge g511 10 0 618 64 (@block_merge g511 10 0 554 64 (@block_merge g511 10 0 490 64 (@block_merge g511 10 0 426 64 (@block_merge g511 10 0 362 64 (@block_merge g511 10 0 298 64 (@block_merge g511 10 0 234 64 (@block_merge g511 10 0 170 64 (@block_merge g511 10 0 135 35 (@block_merge g511 10 0 71 64 (@block_merge g511 10 0 7 64 slice511k10p0 slice511k10p7) slice511k10p71) slice511k10p135) slice511k10p170) slice511k10p234) slice511k10p298) slice511k10p362) slice511k10p426) slice511k10p490) slice511k10p554) slice511k10p618) slice511k10p682) slice511k10p701) slice511k10p765) slice511k10p829) slice511k10p893) slice511k10p957)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p0 : block g511 11 0 44 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p44 : block g511 11 44 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p108 : block g511 11 108 64 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p172 : block g511 11 172 17 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k11p189 : block g511 11 189 57 = true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k11 : block g511 11 0 246=true := (@block_merge g511 11 0 189 57 (@block_merge g511 11 0 172 17 (@block_merge g511 11 0 108 64 (@block_merge g511 11 0 44 64 slice511k11p0 slice511k11p44) slice511k11p108) slice511k11p172) slice511k11p189)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k12p0 : block g511 12 0 9 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k12p9 : block g511 12 9 13 = true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k12 : block g511 12 0 22=true := (@block_merge g511 12 0 9 13 slice511k12p0 slice511k12p9)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem slice511k13p0 : block g511 13 0 1 = true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK511k13 : block g511 13 0 1=true := slice511k13p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem checked511 : checkedTables g511 13 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g511 0 0 0=true)
  · exact (rfl : block g511 1 0 0=true)
  · exact (rfl : block g511 2 0 0=true)
  · exact (rfl : block g511 3 0 0=true)
  · exact (rfl : block g511 4 0 0=true)
  · exact (rfl : block g511 5 0 0=true)
  · exact layerOK511k6
  · exact layerOK511k7
  · exact layerOK511k8
  · exact layerOK511k9
  · exact layerOK511k10
  · exact layerOK511k11
  · exact layerOK511k12
  · exact layerOK511k13
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low511 : Lower (vars 511) (graphGoal 511) 14 :=
  lower_forest (g:=g511) (i:=0) (hints:=34633300) (before_sound known479 valid479) geom511 checked511 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def maps511 : List (Nat × List Nat) := [(511,[])]
def known511 := extendKnown known479 14 maps511
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid511 : Known known511 := extendKnown_ok valid479 low511 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exactLower : ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 9 edge10495 t → 14 ≤ t :=
  conclude10495 (root_index (g:=g511) (before_sound known479 valid479) geom511 checked511 (k:=13) (by decide) (i:=0) (by decide +kernel))

end PEqualNP.Outside.L_meta_10494

theorem PEqualNP.Outside.L_meta_10494 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 6 && x 8) || (x 7 && x 8)) t → 14 ≤ t := PEqualNP.Outside.L_meta_10494.exactLower

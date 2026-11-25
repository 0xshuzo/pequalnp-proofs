import PEqualNP.Defs

-- The Live/Run/Forest checker derives from PressF10, pequalnp-proofs PR 4332,
-- and its extension in L_meta_3853, licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_11008
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
  (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 1 &&& x 8) ||| (x 3 &&& x 8) ||| (x 4 &&& x 8) ||| (x 6 &&& x 8)
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
  (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 1 &&& x 8) ||| (x 3 &&& x 8) ||| (x 4 &&& x 8) ||| (x 6 &&& x 8)
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

def kwFork {U : Finset Sig} {T a b : Sig} {d : Bool}
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms (insert (bin d a b) U) T) : KWRooms (insert a (insert b U)) T := by
  let z := bin d a b
  let sel := fun p n : Row => if d=false then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin false a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin true a b) = (bit r a || bit r b) := by simp [bin,bit]
    cases d <;> cases pA : bit p a <;> cases nA : bit n a <;>
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
      by_cases h : d=false
      · simpa only [sel,h,ite_true] using we
      · simpa [sel,h] using ve


theorem kwTight {T k t S} (run : Live T k t S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction run with
  | stop hp => exact ⟨kwLeaf _⟩
  | @unary k t U a ha hf tail ih =>
    have bound := (live_size (Live.unary ha hf tail)).2
    omega
  | @binary k t U a b d ha hb hab hf tail ih =>
    have fresh : bin d a b∉U := fun h => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := (live_size tail).2
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le (a:=a) (insert b U)
    have le2 := Finset.card_insert_le (a:=b) U
    have na : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at tight
      omega
    have nb : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih eq
    exact ⟨kwFork na nb fresh H⟩
def onlyWire (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v

theorem kwOwn {S T v p n} (H : KWRooms S T) (one : onlyWire S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw

theorem kwCross {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : Impossible T k S := by
  intro j t hj run
  have lb := (live_size run).2
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


def kwR (v s : Nat) : Row := Fin.ofNat 512 ((v >>> s) &&& 511)
def diagTest (T : Sig) (ws : List Sig) (p n : Row) :=
  bit p T && !bit n T && ws.all (fun w => bit p w == bit n w)
theorem diagDone {T ws p n k} (h : diagTest T ws p n = true) : Impossible T k ws.toFinset := by
  intro j t hj run
  simp only [diagTest,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true,beq_iff_eq] at h
  have diff : bit p T ≠ bit n T := by rw [h.1.1,h.1.2]; decide
  obtain ⟨a,ha,ne⟩ := live_row_difference run diff
  exact ne (h.2 a (List.mem_toFinset.mp ha))

def orderTest (T : Sig) (ws : List Sig) (p n : Row) (k : Nat) :=
  decide (k+1 = ws.toFinset.card) && bit p T && !bit n T &&
    ws.all (fun w => !bit p w || bit n w)
theorem orderDone {T ws p n k} (h : orderTest T ws p n k = true) : Impossible T k ws.toFinset := by
  intro j t hj run
  simp only [orderTest,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true,decide_eq_true_eq] at h
  have size := (live_size run).2
  have tight := h.1.1.1
  obtain ⟨a,ha,hp,hn⟩ := mono_row_difference run (by omega) h.1.1.2 h.1.2
  have contra := h.2 a (List.mem_toFinset.mp ha)
  simp [hp,hn] at contra

def kwFull (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let a := ws.getD ((value >>> 2) &&& 15) zero
  let b := ws.getD ((value >>> 6) &&& 15) zero
  let p := kwR value 10
  let n := kwR value 19
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB ws T a p (kwR value 28) && kwWireB ws T b p (kwR value 37) &&
    kwWireB ws T a (kwR value 46) n && kwWireB ws T b (kwR value 55) n
theorem kwFull_sound {T ws k v} (h : kwFull T ws k v=true) : Impossible T k ws.toFinset := by
  simp only [kwFull,Bool.and_eq_true,decide_eq_true_eq] at h
  exact kwCross h.1.1.1.1.1 h.1.1.1.1.2 (kwWireB_sound h.1.1.1.2)
    (kwWireB_sound h.1.1.2) (kwWireB_sound h.1.2) (kwWireB_sound h.2)

def termCheck (T : Sig) (ws : List Sig) (k v : Nat) :=
  if v%4=0 then diagTest T ws (kwR v 2) (kwR v 11)
  else if v%4=1 then orderTest T ws (kwR v 2) (kwR v 11) k
  else kwFull T ws k v
theorem termDone {T ws k v} (h : termCheck T ws k v=true) : Impossible T k ws.toFinset := by
  unfold termCheck at h
  split at h
  · exact diagDone h
  · split at h
    · exact orderDone h
    · exact kwFull_sound h
def mixedBlock (g : Forest) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → nodeVerified g k j=true ∨ Impossible (targetOf g) k (stateSet g k j).toFinset
theorem mixedEmpty (g : Forest) (k a : Nat) : mixedBlock g k a 0 := by
  intro j lo hi
  omega
theorem mixedVerified {g k a n} (h : block g k a n=true) : mixedBlock g k a n :=
  fun j lo hi => Or.inl (block_at h j lo hi)
theorem mixedJoin {g k a x y} (first : mixedBlock g k a x) (last : mixedBlock g k (a+x) y) :
    mixedBlock g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def kwTest (g : Forest) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all (fun j => termCheck (targetOf g) (stateSet g k (a+j)) k (packedAt data (64*j) 64))
theorem mixedCut {g k a n data} (h : kwTest g k a n data=true) :
    mixedBlock g k a n := by
  intro j lo hi
  right
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change termCheck _ (stateSet g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact termDone hh

def mixedTables (g : Forest) (top : Nat) := ∀ k ≤ top, mixedBlock g k 0 (g.levels k).1
theorem mixedForest (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : mixedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible (targetOf g) k (stateSet g k i).toFinset := by
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
theorem mixedRoot {g top prior k i ws} (lower : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : mixedTables g top) (le : k≤top)
    (idx : indexedRoot g k i ws=true) : Impossible (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact mixedForest g top prior lower geom blocks _ le i idx.1

theorem mixedLower {g prior i hints} (low : ∀ q, Lower (vars q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : mixedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) _ (mixedRoot low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def edge11008 : (Fin 9 → Bool) → Bool := fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)
def sample11008 (r : Row) (i : Fin 9) := bit r (inputs.getD i.val zero)
theorem raw11008 : List.ofFn (fun i : Fin 9 => inputs.getD i.val zero) = vars 511 := by decide +kernel
theorem samp11008 (r : Row) : List.ofFn (sample11008 r) = (vars 511).map (bit r) := by
  rw [←raw11008,List.map_ofFn]
  rfl
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem edge11008_table : ∀ r : Row, bit r (graphGoal 511) = edge11008 (sample11008 r) := by decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem conclude11008 (absent : Impossible (graphGoal 511) 14 (vars 511).toFinset) :
    ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 9 edge11008 t → 15 ≤ t := by
  intro t hs
  obtain ⟨C,hf,hsize,correct⟩ := hs
  by_contra! bad
  have hp : proper (graphGoal 511) := by unfold proper; decide +kernel
  have he : (execute C.gates (vars 511)).getD C.output zero = graphGoal 511 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    change bit r ((execute C.gates (vars 511)).getD C.output zero) = bit r (graphGoal 511)
    rw [←b_read,execute_bits _ _ _ (fun g hg => (hf g hg).1),←samp11008,edge11008_table]
    exact correct (sample11008 r)
  have hout := get_rep (execute C.gates (vars 511)) C.output
  rw [he] at hout
  obtain ⟨k,u,S,hk,run,sub⟩ := extract C.gates _ hf hp (hout.resolve_right (fun h => h hp))
  have all : ∀ a ∈ vars 511, Essential (graphGoal 511) (vars 511) a := by
    have valid : checkEssential (graphGoal 511) (vars 511) (graphPairs 511 4832323157) = true := by decide +kernel
    have ident : (graphPairs 511 4832323157).map Prod.fst = vars 511 := by decide +kernel
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
def word328r3 (i : Nat) : Nat := 0x7
def lay328r3 : Packing := (1,0,0,63,0,0,1,word328r3)
def samp328 : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3f,0x49),(0x0,0x0),(0x0,0x0),((~~~(0x38 : Bits)),0x92),(0x0,0x0),((~~~(0x7 : Bits)),(~~~(0xdb : Bits)))]
def cols328 : IndexTree ColumnInfo := (.leaf [])
def lv328 : Nat → Packing
  | 3 => lay328r3
  | _ => emptyPacking
def ix328 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g328 : Forest := ⟨328,3,fun j => samp328[j]?.getD (0,0),cols328,#[[],[134],[99],[99,131],[131,99],[131]],lv328,ix328,noFactory,noFactorySound 328⟩
def word99r3 (i : Nat) : Nat := 0xf
def lay99r3 : Packing := (1,0,0,63,0,0,1,word99r3)
def cut99k3p0 (i : Nat) : Nat := 0x1110402202108482
def samp99 : Array (Bits × Bits) := #[(0x7fc1f,0x11c43),((~~~(0x4f81f : Bits)),0xb556a),(0x0,0x0),(0x0,0x0),(0x0,0x0),((~~~(0x3f800 : Bits)),(~~~(0xb7d6b : Bits))),((~~~(0x7ff : Bits)),(~~~(0x11ce7 : Bits))),(0x0,0x0),(0x0,0x0)]
def cols99 : IndexTree ColumnInfo := (.leaf [])
def lv99 : Nat → Packing
  | 3 => lay99r3
  | _ => emptyPacking
def ix99 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g99 : Forest := ⟨99,3,fun j => samp99[j]?.getD (0,0),cols99,#[[],[80,97]],lv99,ix99,noFactory,noFactorySound 99⟩
def word329r4 (i : Nat) : Nat := 0x1f
def lay329r4 : Packing := (1,0,0,63,0,0,1,word329r4)
def samp329 : Array (Bits × Bits) := #[((~~~(0xf3ef0 : Bits)),(~~~(0x61a54 : Bits))),(0x0,0x0),(0x0,0x0),(0xfff0,0x14732),(0x0,0x0),(0x0,0x0),((~~~(0xfe00 : Bits)),0x20844),(0x0,0x0),((~~~(0x1ff : Bits)),(~~~(0x34f77 : Bits)))]
def cols329 : IndexTree ColumnInfo := (.leaf [(1,0,328,0,4)])
def lv329 : Nat → Packing
  | 4 => lay329r4
  | _ => emptyPacking
def ix329 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g329 : Forest := ⟨329,4,fun j => samp329[j]?.getD (0,0),cols329,#[[],[131]],lv329,ix329,noFactory,noFactorySound 329⟩
def word488r5 (i : Nat) : Nat := 0x3f
def lay488r5 : Packing := (1,0,0,63,0,0,1,word488r5)
def samp488 : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3003ff3c03ff,0x10250b1c4913),(0x0,0x0),(0xcc0300cfff00,0x4d1746451f4a),((~~~(0xf003ff0ffc00 : Bits)),0x1045814e0922c),((~~~(0xfffff0003ff : Bits)),(~~~(0x4d9f67451f4f : Bits))),((~~~(0xffffff : Bits)),(~~~(0x1147d1ffcff3f : Bits)))]
def cols488 : IndexTree ColumnInfo := (.leaf [(0,32,328,128,5)])
def lv488 : Nat → Packing
  | 5 => lay488r5
  | _ => emptyPacking
def ix488 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g488 : Forest := ⟨488,5,fun j => samp488[j]?.getD (0,0),cols488,#[[],[134],[117],[117,134],[99],[99,131],[99,117],[99,117,131],[131,99],[131],[131,117,99],[131,117]],lv488,ix488,noFactory,noFactorySound 488⟩
def word103r4 (i : Nat) : Nat := 0x1f
def lay103r4 : Packing := (1,0,0,63,0,0,1,word103r4)
def cut103k4p0 (i : Nat) : Nat := 0x11104022021084c2
def samp103 : Array (Bits × Bits) := #[(0x1903fe703f,0x9090e3083),(0x6e03039fc0,0x2e4b4a94d2),((~~~(0x7003fc1fff : Bits)),0x8b1c1be28a),(0x0,0x0),(0x0,0x0),((~~~(0xffffc0000 : Bits)),(~~~(0x2f6f6eb4d3 : Bits))),((~~~(0x3ffff : Bits)),(~~~(0x8b1d1ff3cf : Bits))),(0x0,0x0),(0x0,0x0)]
def cols103 : IndexTree ColumnInfo := (.leaf [])
def lv103 : Nat → Packing
  | 4 => lay103r4
  | _ => emptyPacking
def ix103 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g103 : Forest := ⟨103,4,fun j => samp103[j]?.getD (0,0),cols103,#[[],[33,101]],lv103,ix103,noFactory,noFactorySound 103⟩
def word109r4 (i : Nat) : Nat := 0x1f
def lay109r4 : Packing := (1,0,0,63,0,0,1,word109r4)
def cut109k4p0 (i : Nat) : Nat := 0x1091080011210412
def samp109 : Array (Bits × Bits) := #[(0x6820ffff,0x28a21aa3),(0x0,0x0),((~~~(0x64fc0f99f : Bits)),(~~~(0x74e58c995 : Bits))),((~~~(0x1c03ff87f : Bits)),(~~~(0x5c639c875 : Bits))),(0x0,0x0),((~~~(0x3ffff800 : Bits)),(~~~(0x3aeb5aa3 : Bits))),((~~~(0x7ff : Bits)),0x54618c010),(0x0,0x0),(0x0,0x0)]
def cols109 : IndexTree ColumnInfo := (.leaf [])
def lv109 : Nat → Packing
  | 4 => lay109r4
  | _ => emptyPacking
def ix109 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g109 : Forest := ⟨109,4,fun j => samp109[j]?.getD (0,0),cols109,#[[],[50]],lv109,ix109,noFactory,noFactorySound 109⟩
def word229r5 (i : Nat) : Nat := 0xc140fd20fd10fa00
def lay229r5 : Packing := (3,1,3,63,0,5,1,word229r5)
def keys229k6 (i : Nat) : Nat := 0x1840010ea8181001cc4adead8bc0f1a001c12579c0000ca83503
def cut229k5p1 (i : Nat) : Nat := 0x10910c001121040e42084408002a810a
def word229r6 (i : Nat) : Nat := 0x23444bf
def lay229r6 : Packing := (1,0,3,63,0,0,1,word229r6)
def samp229 : Array (Bits × Bits) := #[(0x680c0180ffff,0x2a1d10a246a3),(0x0,0x0),(0x900ffeff0180,0x10543a870d8a),(0x0,0x0),(0x0,0x0),((~~~(0xe00ff8fffe00 : Bits)),0x110e06714291c),((~~~(0x1ffff80001ff : Bits)),(~~~(0x3b7dbaa74faf : Bits))),((~~~(0x7ffffff : Bits)),(~~~(0x110f47f9f3f9f : Bits))),(0x0,0x0)]
def cols229 : IndexTree ColumnInfo := (.fork 2 (.leaf [(1,0,228,0,4),(4,0,225,0,4)]) (.leaf [(32,0,197,0,4),(64,0,165,0,4),(128,0,101,0,4)]))
def lv229 : Nat → Packing
  | 5 => lay229r5
  | 6 => lay229r6
  | _ => emptyPacking
def ix229 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 19 3 10 2 4 keys229k6
  | _ => fun _ => none
def g229 : Forest := ⟨229,6,fun j => samp229[j]?.getD (0,0),cols229,#[[],[114,101],[32,117],[32,80,96,112],[80,118],[80,98,112,32],[96,82],[96,114,80,82],[112,32,82,101],[112,98]],lv229,ix229,noFactory,noFactorySound 229⟩
def word361r5 (i : Nat) : Nat := 0x403ec4920fe33fd41fd31de33f611
def lay361r5 : Packing := (5,1,2,63,0,5,1,word361r5)
def keys361k6 (i : Nat) : Nat := 0x1880002a28d4400000142ab10000000000000000001
def cut361k5p2 (i : Nat) : Nat := 0x109208001141040e109208001141040e109208009141040e
def word361r6 (i : Nat) : Nat := 0x13c7f
def lay361r6 : Packing := (1,0,2,63,0,0,1,word361r6)
def samp361 : Array (Bits × Bits) := #[(0x803c0180ffff,0xa11d10a246a3),(0x0,0x0),(0x0,0x0),(0xcffeff0180,0x3443a870d8a),(0x0,0x0),((~~~(0xff0ff8fffe00 : Bits)),(~~~(0xb51d98ab56a3 : Bits))),((~~~(0xfff80001ff : Bits)),0x10c0045183010),(0x0,0x0),((~~~(0x7ffffff : Bits)),(~~~(0x10f447f9f3f9f : Bits)))]
def cols361 : IndexTree ColumnInfo := (.leaf [(0,32,328,1,5),(8,0,353,0,4),(256,0,105,0,4),(1,32,328,0,4)])
def lv361 : Nat → Packing
  | 5 => lay361r5
  | 6 => lay361r6
  | _ => emptyPacking
def ix361 : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 22 1 8 3 1 keys361k6
  | _ => fun _ => none
def g361 : Forest := ⟨361,6,fun j => samp361[j]?.getD (0,0),cols361,#[[],[131]],lv361,ix361,noFactory,noFactorySound 361⟩
def word331r5 (i : Nat) : Nat := 0x3f
def lay331r5 : Packing := (1,0,0,63,0,0,1,word331r5)
def samp331 : Array (Bits × Bits) := #[(0x20b060907f,0x31b9729933),((~~~(0x3f3f801f9f : Bits)),(~~~(0x3a3cd81a95 : Bits))),(0x0,0x0),(0xff80ff80,0x1d182b182),(0x0,0x0),(0x0,0x0),((~~~(0xffff0000 : Bits)),(~~~(0x39fdfbb9b3 : Bits))),(0x0,0x0),((~~~(0xffff : Bits)),0x382c580810)]
def cols331 : IndexTree ColumnInfo := (.leaf [(1,0,330,0,5)])
def lv331 : Nat → Packing
  | 5 => lay331r5
  | _ => emptyPacking
def ix331 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g331 : Forest := ⟨331,5,fun j => samp331[j]?.getD (0,0),cols331,#[[],[16,134]],lv331,ix331,noFactory,noFactorySound 331⟩
def word333r5 (i : Nat) : Nat := 0x3f
def lay333r5 : Packing := (1,0,0,63,0,0,1,word333r5)
def samp333 : Array (Bits × Bits) := #[((~~~(0x1799f5ef0 : Bits)),(~~~(0x1318d4a54 : Bits))),(0x0,0x0),((~~~(0xf87f3e0f : Bits)),(~~~(0xb06d2a45 : Bits))),(0x7fffe00,0xaa3e622),(0x0,0x0),(0x0,0x0),((~~~(0x7ff0000 : Bits)),0x10040844),(0x0,0x0),((~~~(0xffff : Bits)),(~~~(0x1aa7ef77 : Bits)))]
def cols333 : IndexTree ColumnInfo := (.leaf [(1,0,332,0,5)])
def lv333 : Nat → Packing
  | 5 => lay333r5
  | _ => emptyPacking
def ix333 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g333 : Forest := ⟨333,5,fun j => samp333[j]?.getD (0,0),cols333,#[[],[131],[32],[32,131]],lv333,ix333,noFactory,noFactorySound 333⟩
def word250r5 (i : Nat) : Nat := 0x3f
def lay250r5 : Packing := (1,0,0,63,0,0,1,word250r5)
def cut250k5p0 (i : Nat) : Nat := 0x480884080092814e
def samp250 : Array (Bits × Bits) := #[(0x0,0x0),(0x4cc240330033cc03fff,0x4cc27273ca11cf495d3),(0x0,0x0),(0xfb803c00ccffff300,0x5b917c4644551f34a),((~~~(0x70f3ffc0000f0ffc3ff : Bits)),(~~~(0x7af3f8aae00f0f243c5 : Bits))),((~~~(0xff0003fff00fffc000 : Bits)),(~~~(0x6ff37a7feb11ff6d5d3 : Bits))),((~~~(0xfffffff000003fff : Bits)),(~~~(0x5fd9ff6744551ff4f : Bits))),((~~~(0xfffffffff : Bits)),0x6af3782ae00003000c0),(0x0,0x0)]
def cols250 : IndexTree ColumnInfo := (.leaf [])
def lv250 : Nat → Packing
  | 5 => lay250r5
  | _ => emptyPacking
def ix250 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g250 : Forest := ⟨250,5,fun j => samp250[j]?.getD (0,0),cols250,#[[],[99],[65,117],[65,99,117]],lv250,ix250,noFactory,noFactorySound 250⟩
def word238r6 (i : Nat) : Nat := 0xe413f
def lay238r6 : Packing := (1,0,2,63,0,0,1,word238r6)
def samp238 : Array (Bits × Bits) := #[(0x0,0x0),((~~~(0x336efe67ff89fcfe000 : Bits)),(~~~(0x336e3c61dfc8743b51c : Bits))),(0xe201fff99803ff980,0x220aa87898190f98a),(0xf3c01e00e1ffc01e00,0x53c4be26a1a9c4de2a),(0x0,0x0),((~~~(0xfc001fff01ffffe000 : Bits)),0x10261c00cfc0502951c),((~~~(0x3ffffff0000001fff : Bits)),(~~~(0x53f6ffb7a9a9d4ffaf : Bits))),((~~~(0xffffffffff : Bits)),(~~~(0x10261ea8fffe7f3ff9f : Bits))),(0x0,0x0)]
def cols238 : IndexTree ColumnInfo := (.leaf [(0,2,204,32,5),(0,8,166,64,5),(2,0,236,0,5),(8,0,230,0,5)])
def lv238 : Nat → Packing
  | 6 => lay238r6
  | _ => emptyPacking
def ix238 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g238 : Forest := ⟨238,6,fun j => samp238[j]?.getD (0,0),cols238,#[[],[49,114,101]],lv238,ix238,noFactory,noFactorySound 238⟩
def word243r6 (i : Nat) : Nat := 0x90ff
def lay243r6 : Packing := (1,0,2,63,0,0,1,word243r6)
def samp243 : Array (Bits × Bits) := #[(0x7a80cc013fff9c07f,0x2aa1cd100aa38d123),(0x266300f006d980e7f80,0x266365f33259eaa75ea),(0x0,0x0),(0x0,0x0),((~~~(0x387bff0000e1ff07fff : Bits)),(~~~(0x3d7bf2ab80e1e5072e5 : Bits))),((~~~(0x7f800fff81fff00000 : Bits)),(~~~(0x37fbf5ffba5fefaf5eb : Bits))),((~~~(0x7fffff80000fffff : Bits)),(~~~(0x2fb3fd980aa3fd3a7 : Bits))),((~~~(0x7fffffffff : Bits)),0x357bf0ab80006003060),(0x0,0x0)]
def cols243 : IndexTree ColumnInfo := (.leaf [(2,0,241,0,5),(1,64,178,0,4),(128,16,99,0,4)])
def lv243 : Nat → Packing
  | 6 => lay243r6
  | _ => emptyPacking
def ix243 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g243 : Forest := ⟨243,6,fun j => samp243[j]?.getD (0,0),cols243,#[[],[112,100]],lv243,ix243,noFactory,noFactorySound 243⟩
def word486r6 (i : Nat) : Nat := 0x60a07f4c3fa21fa00
def lay486r6 : Packing := (3,1,3,63,0,5,1,word486r6)
def keys486k7 (i : Nat) : Nat := 0x7a000600c4543eb002000bdec50400095e700000523740c000000230ac0
def cut486k6p1 (i : Nat) : Nat := 0x420884080032810a420884080032810a
def word486r7 (i : Nat) : Nat := 0x34ad19bf
def lay486r7 : Packing := (1,0,3,63,0,0,1,word486r7)
def samp486 : Array (Bits × Bits) := #[(0x0,0x0),((~~~(0x1fcf7f000dbf9ff0fe00 : Bits)),(~~~(0x1fef76ee8db71b78db6c : Bits))),(0x4c900b003807ff3ff80,0x44921b44090a8d147a2),(0x0,0x0),(0x0,0x0),(0x70e00c01cff803c01ff,0x50e24c484930938512c),((~~~(0x7f000ffe0ffffc001ff : Bits)),(~~~(0x17fd71fe60f5fad1c7e7 : Bits))),((~~~(0xfffffe000003fffff : Bits)),(~~~(0x54fb7f6e493a9ff5faf : Bits))),((~~~(0x1fffffffffff : Bits)),0x17ed70ee00301800c060)]
def cols486 : IndexTree ColumnInfo := (.fork 3 (.leaf [(2,0,484,0,5),(34,0,452,0,4),(68,0,418,0,4)]) (.leaf [(132,0,354,0,4),(160,0,326,0,4),(258,0,228,0,4),(320,0,166,0,4)]))
def lv486 : Nat → Packing
  | 6 => lay486r6
  | 7 => lay486r7
  | _ => emptyPacking
def ix486 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 5 22 3 10 2 4 keys486k7
  | _ => fun _ => none
def g486 : Forest := ⟨486,7,fun j => samp486[j]?.getD (0,0),cols486,#[[],[133,118],[33,101,135],[33,117,134],[81,98,135],[81,98,113,130,33],[97,82],[97,82,130,113],[113,130,82,97],[113,130],[129,114,81,98,101],[129,114,101]],lv486,ix486,noFactory,noFactorySound 486⟩
def word489r7 (i : Nat) : Nat := 0x7f
def lay489r7 : Packing := (1,0,0,63,0,0,1,word489r7)
def samp489 : Array (Bits × Bits) := #[((~~~(0x6cf7fe1ffb1bff3fc0000 : Bits)),(~~~(0x6cf3bf0efb99bf9bdba6e : Bits))),(0x0,0x0),(0x0,0x0),(0x3c0067fe738037fc0300,0x1404a2165384944c4b14),(0x0,0x0),(0x1c300780183fff80003ff,0x4322f08c8091f9292a4e),((~~~(0x1fc007ffe03ffc00003ff : Bits)),0x2010b0029a80928b0b028),((~~~(0x3fffffe00003fffffff : Bits)),(~~~(0x43b3fece8091fd3d3f4f : Bits))),((~~~(0x1ffffffffffff : Bits)),(~~~(0x2150fa23fffcffcfcff3f : Bits)))]
def cols489 : IndexTree ColumnInfo := (.leaf [(128,0,361,0,7)])
def lv489 : Nat → Packing
  | 7 => lay489r7
  | _ => emptyPacking
def ix489 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g489 : Forest := ⟨489,7,fun j => samp489[j]?.getD (0,0),cols489,#[[],[131]],lv489,ix489,noFactory,noFactorySound 489⟩
def word366r7 (i : Nat) : Nat := 0x7f
def lay366r7 : Packing := (1,0,0,63,0,0,1,word366r7)
def samp366 : Array (Bits × Bits) := #[(0x0,0x0),(0x2003901ff0760301fff,0x22409148b0364b24a93),((~~~(0x1bfcd1fe7f667fc0067f : Bits)),(~~~(0x1af0d17239766e670635 : Bits))),(0x3cffe00e1ffc01e00,0xd4b0e06a1a1c0de0a),(0x0,0x0),((~~~(0x7fc0fffff01ffffe000 : Bits)),(~~~(0x6b40f57ab03e6f36a93 : Bits))),((~~~(0x3ffffff0000001fff : Bits)),0xa70003018564e270030),(0x0,0x0),((~~~(0xffffffffff : Bits)),(~~~(0xa7d4b3e9fffeff7ffbf : Bits)))]
def cols366 : IndexTree ColumnInfo := (.leaf [(4,0,362,0,7)])
def lv366 : Nat → Packing
  | 7 => lay366r7
  | _ => emptyPacking
def ix366 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g366 : Forest := ⟨366,7,fun j => samp366[j]?.getD (0,0),cols366,#[[]],lv366,ix366,noFactory,noFactorySound 366⟩
def word365r7 (i : Nat) : Nat := 0x7f
def lay365r7 : Packing := (1,0,0,63,0,0,1,word365r7)
def samp365 : Array (Bits × Bits) := #[(0x5001f980068080fffff,0x5420b9a202a2a246aa3),(0x0,0x0),((~~~(0x19fe661ff64ff00fe67f : Bits)),(~~~(0x19386619974991832615 : Bits))),(0x1e1fffe3ff0001e00,0x6a0a87a387060de0a),(0x0,0x0),((~~~(0x7fe01fff03fffffe000 : Bits)),(~~~(0x76a0bfb303abab56aa3 : Bits))),((~~~(0x1fffff00000001fff : Bits)),0x8180000854181830010),(0x0,0x0),((~~~(0xfffffffffff : Bits)),(~~~(0x81ea0a8fff9f9f3ff9f : Bits)))]
def cols365 : IndexTree ColumnInfo := (.leaf [(4,0,361,0,7)])
def lv365 : Nat → Packing
  | 7 => lay365r7
  | _ => emptyPacking
def ix365 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g365 : Forest := ⟨365,7,fun j => samp365[j]?.getD (0,0),cols365,#[[],[131]],lv365,ix365,noFactory,noFactorySound 365⟩
def word335r6 (i : Nat) : Nat := 0x7f
def lay335r6 : Packing := (1,0,0,63,0,0,1,word335r6)
def samp335 : Array (Bits × Bits) := #[((~~~(0x6fa69f33eadf6f80 : Bits)),(~~~(0x67268d31aacd66cc : Bits))),(0x206180fff9c0e060,0x22e18654f9cae56a),((~~~(0x3f81ff0fe1ff007f : Bits)),(~~~(0x3701ed0da1ed466d : Bits))),(0x7fff001fff0000,0xeba3005f630102),(0x0,0x0),(0x0,0x0),((~~~(0x7fffffe0000000 : Bits)),0x23000400808c464c),(0x0,0x0),((~~~(0x1fffffff : Bits)),(~~~(0x23eba754ffeff7ef : Bits)))]
def cols335 : IndexTree ColumnInfo := (.leaf [(1,0,334,0,6)])
def lv335 : Nat → Packing
  | 6 => lay335r6
  | _ => emptyPacking
def ix335 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g335 : Forest := ⟨335,6,fun j => samp335[j]?.getD (0,0),cols335,#[[],[32]],lv335,ix335,noFactory,noFactorySound 335⟩
def word231r7 (i : Nat) : Nat := 0x7f
def lay231r7 : Packing := (1,0,0,63,0,0,1,word231r7)
def samp231 : Array (Bits × Bits) := #[(0x1ea033001901ff9c07f,0xaa873440944a38d123),((~~~(0x1a73fc3ff91fe7f1807f : Bits)),(~~~(0x1a727833bd13a1d58e1d : Bits))),(0x61003fff8ffe00f8000,0x101550e8b0e06f850a),(0x0,0x0),(0x0,0x0),((~~~(0x7e003ffe0fffff00000 : Bits)),0x81038019d0281450e1c),((~~~(0x1fffffe000000fffff : Bits)),(~~~(0xbedff6e8b4ea7fd7af : Bits))),((~~~(0x1fffffffffff : Bits)),(~~~(0x8103d51fff3f9ffcf9f : Bits))),(0x0,0x0)]
def cols231 : IndexTree ColumnInfo := (.leaf [(2,0,229,0,7)])
def lv231 : Nat → Packing
  | 7 => lay231r7
  | _ => emptyPacking
def ix231 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g231 : Forest := ⟨231,7,fun j => samp231[j]?.getD (0,0),cols231,#[[],[112,98]],lv231,ix231,noFactory,noFactorySound 231⟩
def word363r6 (i : Nat) : Nat := 0x18930c0bf99954bb58854be58054cf95644e791233
def lay363r6 : Packing := (5,2,3,63,0,5,1,word363r6)
def keys363k7 (i : Nat) : Nat := 0x40000026a4ca10a01538
def cut363k6p4 (i : Nat) : Nat := 0x1092080011410412
def word363r7 (i : Nat) : Nat := 0x10e62a5a9835959084146a988ea623b90921201fd54fe2a7f9137c89de33
def lay363r7 : Packing := (5,1,3,63,0,7,1,word363r7)
def keys363k8 (i : Nat) : Nat := 0x7a00d950310000b300d412
def word363r8 (i : Nat) : Nat := 0x468897f
def lay363r8 : Packing := (1,0,3,63,0,0,1,word363r8)
def samp363 : Array (Bits × Bits) := #[(0x1001d806001900ffe700ff,0x1410da1684094250e34243),(0x20026007fe6e00c039ff00,0x20906052162e12c4a91312),(0x0,0x0),(0xc7ff8018fff003e0000,0x3468380c8b0701be0a0a),(0x0,0x0),((~~~(0x3ff07ffffe0fffffc00000 : Bits)),(~~~(0x36d0fb5ed62f5bd6eb5353 : Bits))),((~~~(0xffffffe0000003fffff : Bits)),0x61c000c03174388e003030),(0x0,0x0),((~~~(0x1ffffffffffff : Bits)),(~~~(0x61f468fa3fff3fcfff3f3f : Bits)))]
def cols363 : IndexTree ColumnInfo := (.fork 3 (.leaf [(1,0,362,0,7),(2,0,361,0,7),(8,0,355,0,7)]) (.leaf [(0,32,328,3,6),(32,0,331,0,6),(64,0,299,0,5),(256,0,107,0,5)]))
def lv363 : Nat → Packing
  | 6 => lay363r6
  | 7 => lay363r7
  | 8 => lay363r8
  | _ => emptyPacking
def ix363 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 11 3 8 3 1 keys363k7
  | 8 => lookupWord 2 11 0 8 3 1 keys363k8
  | _ => fun _ => none
def g363 : Forest := ⟨363,8,fun j => samp363[j]?.getD (0,0),cols363,#[[],[16,134]],lv363,ix363,noFactory,noFactorySound 363⟩
def word251r7 (i : Nat) : Nat := 0xff
def lay251r7 : Packing := (1,0,0,63,0,0,1,word251r7)
def samp251 : Array (Bits × Bits) := #[(0x93ca500cccc002193e403ff9ce700ff,0x914a541cccd0800916509438c634243),(0x4ce30c600f0f000c6e3380300e739ff00,0x4ce30c6c9f0f32842e33b4bd2a529d3d2),(0x0,0x0),(0xfc2f800ff000318fc3ffc00f83e0000,0xb42f845ff011908b42d1c46f83e4a4a),((~~~(0x70ffcffff0000001f003fffff003fffff : Bits)),(~~~(0x7affcffe2aaab801f003f27c9003fc5c5 : Bits))),((~~~(0xfffc0000fffffc00ffffffff00000000 : Bits)),(~~~(0x6fffcf7e9ffffac42ffff6fdbad6bd3d3 : Bits))),((~~~(0x3fffffffffc0000000000ffffffff : Bits)),(~~~(0xb57ff67fffd9d08b56d1d47ffff4f4f : Bits))),((~~~(0x3ffffffffffffffffff : Bits)),0x6affcf7e0aaab8000000300c00000c0c0),(0x0,0x0)]
def cols251 : IndexTree ColumnInfo := (.leaf [(2,0,249,0,7)])
def lv251 : Nat → Packing
  | 7 => lay251r7
  | _ => emptyPacking
def ix251 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g251 : Forest := ⟨251,7,fun j => samp251[j]?.getD (0,0),cols251,#[[]],lv251,ix251,noFactory,noFactorySound 251⟩
def word381r8 (i : Nat) : Nat := 0xff
def lay381r8 : Packing := (1,0,0,63,0,0,1,word381r8)
def samp381 : Array (Bits × Bits) := #[(0x280003eb301980041a4e8080fffffff,0x2a10016b3459a2000a46a2a246aaaa3),(0x0,0x0),(0x2300b3333c01e009a6c7300ff0199980,0x2363b3333ccde668a2c5366e7cd999ea),(0xc3c3c001fffe38f83ff0001e1e00,0x3c143c00ca87a28e8387060de1e0a),((~~~(0x3bff03fc0001fff03f003fffffe01fff : Bits)),(~~~(0x3bf42bfc2ae1ff103f003e9e9d201fe5 : Bits))),((~~~(0x7ff0003fffffff000ffffffffe00000 : Bits)),(~~~(0x7b50017ff67fb3000fffabab56aaaa3 : Bits))),((~~~(0xfffffffffff000000000001fffff : Bits)),(~~~(0x33f3ffffffefff7aaaed7e7e7cffffef : Bits))),(0x0,0x0),((~~~(0xfffffffffffffffff : Bits)),0x33f02abc2ae15700000006060c000060)]
def cols381 : IndexTree ColumnInfo := (.leaf [(4,0,377,0,8)])
def lv381 : Nat → Packing
  | 8 => lay381r8
  | _ => emptyPacking
def ix381 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g381 : Forest := ⟨381,8,fun j => samp381[j]?.getD (0,0),cols381,#[[]],lv381,ix381,noFactory,noFactorySound 381⟩
def word247r8 (i : Nat) : Nat := 0xff
def lay247r8 : Packing := (1,0,0,63,0,0,1,word247r8)
def samp247 : Array (Bits × Bits) := #[(0xf1402b300cc002193e403ff9ce700ff,0x51506b342cd0800916509438c634243),(0x132c18033c00f000c6e3380300e739ff00,0x132c1b273ccaf32842e33b4bd2a529d3d2),(0x30a003c000ffff18fc3ffc00f83e0000,0xa017c006541d08b42c1c06f83e0a0a),(0x0,0x0),((~~~(0x1c3f3ffc0000fffc1f003fffff003fffff : Bits)),(~~~(0x1ebf3f882ae0ff841f003f27c9003fc5c5 : Bits))),((~~~(0x3ff0003fffffffc00ffffffff00000000 : Bits)),(~~~(0x1bff1fa7ffebffac42ffff6fdbad6bd3d3 : Bits))),((~~~(0xfffffffffffc0000000000ffffffff : Bits)),(~~~(0x5fd9fff67fd9d08b56d1d47ffff4f4f : Bits))),((~~~(0x3ffffffffffffffffff : Bits)),0x1abf1f802ae0ab8000000300c00000c0c0),(0x0,0x0)]
def cols247 : IndexTree ColumnInfo := (.leaf [(2,0,245,0,8)])
def lv247 : Nat → Packing
  | 8 => lay247r8
  | _ => emptyPacking
def ix247 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g247 : Forest := ⟨247,8,fun j => samp247[j]?.getD (0,0),cols247,#[[],[32,65,117]],lv247,ix247,noFactory,noFactorySound 247⟩
def word239r8 (i : Nat) : Nat := 0xff
def lay239r8 : Packing := (1,0,0,63,0,0,1,word239r8)
def samp239 : Array (Bits × Bits) := #[(0x487a8a0333300035202407fe739c07f,0x482a8a873334401528a5128e318d123),((~~~(0x18e9cf3fc3c3fff263fc7f9fc631807f : Bits)),(~~~(0x18e9cf2783c33bfa62744e8756b58e1d : Bits))),(0x1841003fffff31e003ff803e0f8000,0x410155550f11e01ac381be0f850a),(0x7e07e003fc001c1fffc00003ff00000,0x5a07e097fc04d41f69c1309bff0152a),(0x0,0x0),((~~~(0x7ff80003ffffe01ffffffffc0000000 : Bits)),0x8004303800019fa00500a0514a50e1c),((~~~(0x7ffffffffe00000000003fffffff : Bits)),(~~~(0x5a2ffedffff6f51f69ed3a9ffffd7af : Bits))),((~~~(0x1ffffffffffffffffff : Bits)),(~~~(0x8004303d5551ffffe7fcfe7ffffcf9f : Bits))),(0x0,0x0)]
def cols239 : IndexTree ColumnInfo := (.leaf [(2,0,237,0,8)])
def lv239 : Nat → Packing
  | 8 => lay239r8
  | _ => emptyPacking
def ix239 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g239 : Forest := ⟨239,8,fun j => samp239[j]?.getD (0,0),cols239,#[[],[49,114,101]],lv239,ix239,noFactory,noFactorySound 239⟩
def word494r6 (i : Nat) : Nat := 0x18c18ae885917219351ac8c10c919eaa5918219200
def lay494r6 : Packing := (3,4,5,63,0,4,1,word494r6)
def keys494k7 (i : Nat) : Nat := 0xb70680
def cut494k6p0 (i : Nat) : Nat := 0x8211000000000000821100000000000082110
def word494r7 (i : Nat) : Nat := 0x18212007021c005001000078d820c341c00500100000003021c004000000000002bd58a95328d409d4d25d28914722d1085411ece86d3317cb8592510c7835190bc58291307c30150903c18090300c00ded829dd64dee771c964ded731c964dec725c164bed8219153bf98019153fac8259140ebd6458940ebd6458540abe8859064eac8259064cbd645c864e9d6419233ead6419222eb964192009ed829dd649ee885c8649fa885c064bcd8219233bd58119233bd98019233e9e6691233f1e5591233ead64589429ec8759222bcd8319222be98019222eae6691222ece668ce22f4e558ce22f8e448ce22e7a6695600be98219200bf18119200eba6691200f3a5591200eea6688a00f6a5588a00faa4488a00fb24484600fe22284600cad645c864
def lay494r7 : Packing := (42,3,5,63,0,9,1,word494r7)
def keys494k8 (i : Nat) : Nat := 0x80d9162d2632b7a4516c12c511f536c9409ae672ef0b0f000000000006e391b13c00280b894512980002b928006a1000000002e2c41e3254800e3a0038472824e11b07110544f53a294dd079408d7c921e88d2b9c794c0718970980c664f390700b1200020258527cd0600480e03d799b4a3
def cut494k7p0 (i : Nat) : Nat := 0x82110
def cut494k7p27 (i : Nat) : Nat := 0x8211000000000000821100000000000082110000000000008211000000000000821100000000000082110
def cut494k7p33 (i : Nat) : Nat := 0x24210084040110c6420884080032810a2228100043021052420884080032810a24210084044110c624210084044110c242088408003280ca242100c4045111c6420884080032810e
def word494r8 (i : Nat) : Nat := 0x1a305880e1828406080a0b3263c38114a1018100886cc1010116a450e0a0051400a0200a0200a1830c1400c0051408a0128a0022020384040171c203020068b08184088330a3400c204c87105a4400a0060420a04500180802460a30438406080c03438006003001800c300143001430010d181828030304060410b140020011096018900020011024c0699209302080e10181805070e10181162c0060023440407080c030440044188058432aa49610c881308c0a99542126052d0849810608080c10b1a00230407092458d0010224c07001450221e3a047001440a2060028414208188990d42038e9cc151bab4880f395c58cb0bd41c4510104526155262930c041129864c2aa4c5261930aa9314a9ca6ca3ca0c9dc9ac97c94c91c8ec8bc88c85c82c7fc7cc79c76c73c70c6dc6ac67c64c61c5ec5bc58c55c52c4fc4cc49c46c43c40c3dc3ac0dbf93e13ccbc63bfbb5babba1b9b394b8e387b7db73b6d351b3d336b30322b1c315b04afe2f7af12e72e0ad6ad02c9aae2a7aa129aa9428a28027625e249a4323ca2ba2521ea112001e49d01c99c31a419d98c97b96715294192992310b1048f70f08e68d90d28cc0c58bf0b88b20af09387805904f04883e83802e02782101701080a0007fe77593feb9ac9ff5c964ffae0b27fe66913feb22c7ff91163ffac8a9ffc6454fff222a7ff99943ffac8a1ffd6550bfeb2285ff55142ffac6a17fd5350bfea1a85ff59132ffac8b07fe44583feb12c1ff50960ffa82b07fd64543ff222a1ff58950ffa84a87fd64503feb1281ff50940ffac2a07fd41503feb2241ff58520ffa82907fd64443fea12217f9dd64fd8e4b25fd72192feb80c9ef1da44dfccd227bd649137f332c7ef91163f7c88a9efe6650fdf22287f799a33fbac919fdc648cfef224677f9dd42bfaeca16fe6650bbf2aa85ef59142f7c88a17de3350bf6b1285bf99932f7c88997ed6488bf632445fb91222fdac7117ed5388bf6a1c457f9dd60dfcccb077e55583df222c1fb88960dfccca87be44543f7112a17f9dd40bfaeca06fe66503bf2aa81ef59140f7c88a07ee22503fcb0281fe54140bfcee905fd764837f33241df95520bfae8907be44483f6b1241fb48520ff2c0907f950483fca02417f5d110f7c88885fd72443f711221fe50110ff4cd007f964803fc32401fe91200ff2c5007f942803fcb0c01fe50600ff243006bd64192eeb98c97b5c864bf2e0326be669136f33467d795633f3c8919fae4488be719c45be99a00ef4ab007ba44803f511401fc84600
def lay494r8 : Packing := (127,2,5,63,0,12,1,word494r8)
def keys494k9 (i : Nat) : Nat := 0x656697c1621c8ab987edcc99d0ff01732dbd911b6ad3b740a06de92b9eb0c486342da11210d4652147b3b84d46833624a152898c5fafc85f98d52bf62106cbc27891623456c733fce00b0baf8725e98344f1767a293b28e63657dbc7cb35def0ff74f261d9b8b75d7db0dd4e5c19ac310f79fa12b100e15b6bcb0207a8bf58a00020e800049800336c3831d78f29ebf4f57487148b303888000003bee8b4af242eecfb90b180000071b6e9867c928002ba80000020ce1f98300048c50042ae9a9e63228000000884eef0916dd2e3bb82e800737a7ef4d80054c6853a68002e58000001250005f88000000840001196c78001cadde000234aad22dce02295aa4370006a3ad2559c68c3259a0a4003aef014dbe2d3682d6273a32cd3d0c2416e715062205c32a1c5b81e00029bef9450d3506708ab95bd8e55728001be2e2b61c66e4a0ba25b611f727426529b935b58610003bd10009021000209105c00000080c6001199f082c604060030e5e2c0860c40015041400b2e000060a000a90201d063ad01010031301
def cut494k8p14 (i : Nat) : Nat := 0x82110
def cut494k8p89 (i : Nat) : Nat := 0x420884080032814e2228100043021056420884080032814e420884080032814e242100840441110622281000430210562421008404411106222810024302105624210084044111062421008404411106222810004302105622281000430210562421018404411106420884080032814e504080420c0088c2242101840441110624210184044111062228100043021056420884088072814e420884080032814e242100840441110624210084044111062421018404411106420884080032814e425008104c011052242100840441110624210084044111062421018404411106420884080032814e242100c404511106242101c404511106420884080032814e420884080032814e420884080032814e420884080032814e420884080032814e420884080032814e2421018424511106
def word494r9 (i : Nat) : Nat := 0x1850881e2aa9a18185556aa9207a488955aaa479c72224094e620788a1899881e24094e62071850aaa59a192075824094e81cb88f6aa2672076222862672073e262a26720760f0aa589a185622894660221eaa654a2a8992aa428cf8aa264afa8294a287f9d4679684e108360a21e0540d81e003fd64ff193fe44ff58ffd53ff50ffd42ff4cbfd60ff543fd40ff483fd10ef913de33fb88bfa00
def lay494r9 : Packing := (17,1,5,63,0,10,1,word494r9)
def keys494k10 (i : Nat) : Nat := 0xe6800000002200000000000013700000000000000000000556000d400444000000049ff0001e651000000e0b1200217480012180000000b4d0cb19ce006500000000000d300143b1c0058400501c518b92801d68a00000
def word494r10 (i : Nat) : Nat := 0x12931ff
def lay494r10 : Packing := (1,0,5,63,0,0,1,word494r10)
def samp494 : Array (Bits × Bits) := #[(0x0,0x0),((~~~(0x1f79efff8dff000cdbbfe67ffe27fcff8000 : Bits)),(~~~(0x1f7dee77edcdb98cdbb3c6677f2674ced59c : Bits))),(0x41920065c00c00038801fffe66003ffe600,0x409241e5c86d0c00890aaa1e2621943e68a),(0xe000079fff0003cf001e00387ffc007800,0xa0009a961702c14f04be09a8689c13782a),(0x0,0x0),(0x701c007e000001c0fffe0003f8000007fff,0x501c457e08c11840991c0233f02504a549c),((~~~(0x7fe0007ffffffe00fffffffc00000007fff : Bits)),(~~~(0x17ffae9fffd7fae14ff6ffedea6e9dd3ffaf : Bits))),((~~~(0x1ffffffffffe0000000003fffffffffff : Bits)),(~~~(0x509f67ffecfd9e40991eaa3fffa7f4ffe9f : Bits))),((~~~(0x1fffffffffffffffffffff : Bits)),0x175dae0569c0b80000300060000600c00180)]
def cols494 : IndexTree ColumnInfo := (.fork 13 (.fork 6 (.fork 3 (.leaf [(2,0,492,0,8),(4,0,490,0,8),(8,0,486,0,8)]) (.leaf [(32,0,462,0,8),(128,0,366,0,8),(0,32,332,130,7)])) (.fork 3 (.leaf [(0,128,330,36,7),(64,0,430,0,7),(256,0,238,0,7)]) (.leaf [(34,0,460,0,7),(132,0,362,0,7),(0,2,204,288,6),(0,4,298,192,6)]))) (.fork 7 (.fork 3 (.leaf [(0,8,166,320,6),(2,32,332,128,6),(2,128,328,36,6)]) (.leaf [(4,32,328,130,6),(6,0,488,0,6),(32,128,330,4,6),(128,32,332,2,6)])) (.fork 3 (.leaf [(10,0,484,0,5),(64,4,298,128,5),(64,8,166,256,5)]) (.leaf [(72,0,422,0,5),(256,2,204,32,5),(256,8,166,64,5),(258,0,236,0,5)]))))
def lv494 : Nat → Packing
  | 6 => lay494r6
  | 7 => lay494r7
  | 8 => lay494r8
  | 9 => lay494r9
  | 10 => lay494r10
  | _ => emptyPacking
def ix494 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 4 0 6 2 0 keys494k7
  | 8 => lookupWord 20 74 5 11 6 1 keys494k8
  | 9 => lookupWord 65 223 7 12 7 1 keys494k9
  | 10 => lookupWord 9 67 3 10 5 1 keys494k10
  | _ => fun _ => none
def g494 : Forest := ⟨494,10,fun j => samp494[j]?.getD (0,0),cols494,#[[],[33,117,134]],lv494,ix494,noFactory,noFactorySound 494⟩
def word493r6 (i : Nat) : Nat := 0x18c14f9961d150482be3223a2a09052b6587450920
def lay493r6 : Packing := (3,4,5,63,0,4,1,word493r6)
def keys493k7 (i : Nat) : Nat := 0x15600016
def cut493k6p0 (i : Nat) : Nat := 0x6110
def cut493k6p1 (i : Nat) : Nat := 0x20a100840c0110c2841108100065010a
def word493r7 (i : Nat) : Nat := 0x370b0230dc2c08c0000000a29c96908a847e78726c66605a3c1e18120c06009fd809dd42bf980911509fd819dd409fd811d120df87454120fe942541209fe885d110ff14150110dac7450920f1e55912338fd869dd42f4e558ce22f8e448ce228fd861d1209f5811d120f3a5591200f6a5588a00faa4488a00fb24484600fe22284600
def lay493r7 : Packing := (20,3,5,63,0,8,1,word493r7)
def keys493k8 (i : Nat) : Nat := 0x3c382264885d02000000400001076a11388972600305000000a8f2250691fc898258d54000182d90384c04e3a5351821e0428e400051b001
def cut493k7p11 (i : Nat) : Nat := 0x6110
def cut493k7p12 (i : Nat) : Nat := 0x20a100840409110620a10084040110c2109108001121041242084408002a814e425008004c01100e20a1018404411082109108001121041242084408002a80c6
def word493r8 (i : Nat) : Nat := 0x25488d1214032446122050021018100a858c14203040500d9e183010050010e1a50b922a00a2c2087c80e3650a801800a3060200a1800a1800860b0e1828406080c0a8002001000c01650380084060650b1438681286cb0018028ac6a5388952272a22508305870c14203054400554990544800962a9c4419600295105001420a9911488654329444a644522155222532229bf36669ccd98f3065dcb595f2a651c9d92f24645c5b88f0ea16bfd78cee5d2b986ecd89a7325630c2d7f2ea5acb093b2694b893d1a2273fc754e41ad3165a49591e1f83bc630b914a260458770d417424835050050007fe4454fff22287ff54d42ffa86a17fe44543fea12a1ff9dd40ffc88a07fd72503fea1281ff5c540ffa82a07fd41483ff22221ff50910f7cef227bd73913deb9489ef5c244bfae5225fd70913df222a7ef91143fbc8919dfe7750bdf22285f78cd42bf8e8997be444cbf722445fb54e22fda87117be44543f7112a17f9dd40efcaaa07be44503f7112817f9dd20efcaa905fd74482fe3a241ef91120fda84907f950483fca02417f5d110f7c88885fd72443f711221fe50110ff489007f942803fca0c01fe48600ebcab19f9e448cfd722445f38ce22ef4ab007ba44803f511401fc84600
def lay493r8 : Packing := (63,2,5,63,0,11,1,word493r8)
def keys493k9 (i : Nat) : Nat := 0x16f7a5246c000000038000000094000000063c1722b5c14e94b4608000002e04000000000000000000000830000000000001d34000001aab8c345c003a9cc3c000003434000000000000000cb00032785d70cc001ee542c0000029440bda74001ab840f9d800000000000249ed66d525e4000000001c5941c00094aaec0019ac003ea000000267c0c98f86dcd74000000e268e40010d8ab3c79920c42477a3000384c0020541850f4002c50000d3a52902400208ab5d884e9000084bc7221bbc8788a1359226de200d222cd06020000002828000000003c0b0e24ba4040009b5d129f000000118a8af25c0038928c6c00c18000000ee855b7502c9c6b4111821ec8d4003e0dad4000464196e68000001664001a8bc980a4000a4e0a897ecf125800188e8478a29174de880000001c7e4ec000000400000000000c00483040c500040000202040570408000061c00012042070204200
def cut493k8p48 (i : Nat) : Nat := 0x1091080011210412224205040921210a1091080091610412222810004302105620a10084040911062421018404411106245020008204209a20a100a40409110620a100a40409110620a101a40449110620a100a40409110620a80c001600840e42084408002a814e42084408002a814e42084408002a814e
def word493r9 (i : Nat) : Nat := 0x38cb554ab44e3544909ca7d442520e32b4d054ca9e41494a18f512bca75549121cad25112d44908480554d12235524494d0546755491261ac5448d3d9a4b4481c8a8360f003fe44ff54ffd43ff50bfd32ff543fd40ff483fd10ef913de33fb88bfa00
def lay493r9 : Packing := (13,1,5,63,0,9,1,word493r9)
def keys493k10 (i : Nat) : Nat := 0x3256abe0de086000f5ea384f560100000845c3014000000042c000020000107001e60000070b4993000e64d8000c8000006880072b2750001b
def word493r10 (i : Nat) : Nat := 0x52511ff
def lay493r10 : Packing := (1,0,5,63,0,0,1,word493r10)
def samp493 : Array (Bits × Bits) := #[((~~~(0x3b33ebfff033ffdcbbff33fff97feffc000000 : Bits)),(~~~(0x3b33e96efa316ddeb95e315dfd2ba5755ca95c : Bits))),(0x0,0x0),(0x80f9800ccf000048800ffff9b001ffc00cc00,0x8059983ccf18600898555878b30d61d86cd8a),(0xf00000f0ffff38f000f000e3ffe00000f000,0x50001350541728f025f026a384e09826f02a),(0x0,0x0),(0xf00e000ff0000c0ffff0000fc00000000ffff,0x900e10afa010c40990e010cfc22845114a91c),((~~~(0xfff0000ffffff00ffffffff0000000000ffff : Bits)),0x1000202c000028d600480048540b0160580050),((~~~(0xffffffffff0000000000ffffffffffffff : Bits)),(~~~(0x905fdcffffdcf40998f558fffb3f67d9ffd9f : Bits))),((~~~(0xffffffffffffffffffffffff : Bits)),(~~~(0x1050203f50543ffffc7ffc7fff8ff1fc7ffc7f : Bits)))]
def cols493 : IndexTree ColumnInfo := (.fork 12 (.fork 6 (.fork 3 (.leaf [(1,0,492,0,8),(4,0,489,0,8),(8,0,485,0,8)]) (.leaf [(32,0,461,0,8),(128,0,365,0,8),(256,0,237,0,8)])) (.fork 3 (.leaf [(0,32,332,129,7),(0,128,329,36,7),(33,0,460,0,7)]) (.leaf [(132,0,361,0,7),(264,0,229,0,7),(0,8,165,320,6)]))) (.fork 6 (.fork 3 (.leaf [(0,256,165,72,6),(64,0,429,0,6),(1,128,328,36,6)]) (.leaf [(4,32,328,129,6),(5,0,488,0,6),(32,128,329,4,6)])) (.fork 3 (.leaf [(128,32,332,1,6),(160,0,333,0,6),(9,0,484,0,5)]) (.leaf [(64,8,165,256,5),(64,256,165,8,5),(129,32,332,0,5)]))))
def lv493 : Nat → Packing
  | 6 => lay493r6
  | 7 => lay493r7
  | 8 => lay493r8
  | 9 => lay493r9
  | 10 => lay493r10
  | _ => emptyPacking
def ix493 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 5 0 6 2 0 keys493k7
  | 8 => lookupWord 10 37 4 11 5 2 keys493k8
  | 9 => lookupWord 42 203 7 12 6 2 keys493k9
  | 10 => lookupWord 8 43 3 10 4 2 keys493k10
  | _ => fun _ => none
def g493 : Forest := ⟨493,10,fun j => samp493[j]?.getD (0,0),cols493,#[[],[131],[32,117],[32,131,117]],lv493,ix493,noFactory,noFactorySound 493⟩
def word487r6 (i : Nat) : Nat := 0x47ea648750e00
def lay487r6 : Packing := (1,4,5,63,0,0,1,word487r6)
def keys487k7 (i : Nat) : Nat := 0x6
def cut487k6p0 (i : Nat) : Nat := 0x111040020210849a
def word487r7 (i : Nat) : Nat := 0x3c100000000085040000000800000000d0cac4beb8b2aca6a09a948e8882746e68625c5650423c36302a241e18120c06009fd809dd43df9809dd43dfa771c143df9711c1439fd809dd41fb88050d419fc874c941f7554545419fe885d130f9d4350530fd9434c110bf98348110ff14148110ff13148110f9d434c941b9e8850c43f988050c43d9d435c043f954310e11f994310e009f9809dd43bd5811d2338fd869dd41f365591211f56558ce11f96448ce11fc63388a119f88750e00f9a448ce00f725584600fb24484600fd23384600fe22284600
def lay487r7 : Packing := (33,3,5,63,0,8,1,word487r7)
def keys487k8 (i : Nat) : Nat := 0xa3e484e2900ca1e000000001036807c3a000000001b0fc2f21540202bf84000000000001f3b0a903dc00e8f026b16c2c9bbab6000001212000aab033240001208001e0f0ba98e0000016165360014a702468cc3922312f303c35e11c18001430805bb7c2100a21b92ce1c620260b00083200050528
def cut487k7p13 (i : Nat) : Nat := 0x210880000000000021088000000000002108800000000000210880000000000021088
def cut487k7p19 (i : Nat) : Nat := 0x20a100840409110a111040020210849e420884080032810a420884082032810a20a100840409110a222810004302104e20a100c60409110a111040220210848211104022021084c210a100c4040911ca222810004302104e10910c001121058e42084408002a80c642084408203280c6
def word487r8 (i : Nat) : Nat := 0x542a0203c5888c1011f2931c807883058a121828406080a0af263c58504a0c1005024500509901e4660b0a0060200a0951e1c1060822c5481f200052078911004147c88e220091881f186060804824306080800914182012048b041400890a2082714305080238e18300900c48b04110087868a005001460c04114086002881470020c1018202446182c509080c101a00025098681200040020010c141829034616182c0909c78f001060a40f9200218203042458008a0c1420312340060081f1851e22048987c88d345909e4810c08600284149002420a104080822909e2910c8864278a042a21fe3faff2fdffb3f4fe6fc7f83eefdafaff53e8fcef97f23e2fc2f7fef3dcfb6f67ec3d6faaf4fe93d0f9ef14dd7b273b64dc497d2f3ddab8d6aecf591adf5369cd1ea153be5fc968db18229c2a7f4f45e23a972ae21bdb676b4d35a032c5f8af958a8f5049d5342384027d0e91c533863caf95226e4547d0d81962f8588a412020c3b0700b81201d82e034034007fe7750ffeb8a87ff5c143ffc8919ffe44547feaa283ff50d41ffaa898ffe444c7fea9a63ff50d31ffa8498ffd324c7feba261ff91130ffa86987fd724c3feb1261ff50930ffa64987fd714c3fea8a61ff50530ffa62987fd214c3feaa221ff91110ffaa6887fd43443fea1221ff4c910ffa86a8ffd32507fea1a437f9dd43ff0e0a1dfd7110efeb8087f71d233f7c8919fdd438ceff3baa3ef91151fbc66a8dfe77506febaa83ef91141f7a86a0fde33507faa8a837f9dd31bfaea98dfd744c7df22263f78cd31feaa298dfe77486feb9a43f78cd21fea8290ff554847fb22423fd54e11fea8708ff443847fb19c23fd50a11fea6508dfe774c2feba261ef91130fba86987de334c3f711261fd84530bfcee885fd75443bf2aa217f5d110f7c88885fd73443ef19a217f5c910fdc44887f541443fa98a21fe4c110ff240887f943803fc21c01fe8ce00ff2a3007f941803fc98c01fe48600f3a8621f9e448cfbb2ac23ed91211fac6708fe622847ed19c01fc84600
def lay487r8 : Packing := (103,2,5,63,0,11,1,word487r8)
def keys487k9 (i : Nat) : Nat := 0x8836b2d64aee3184c0a09315145c10bfb4ff96474c6368850ca3684a06a157354c5a52fa04acdb29f613dc03961017c493234629785ca7e0b307c557900392a6a55ca23be02815c0002dc00008aea6a48b981a08241a450ac2795ac4d2e20007b312a1221433000348ae5af5e028e926e300001b692a605154bd7291a829d2216030559c2588e715685d31d0003361c0163a72da84b3b894a20089286ac80300062834960000000000000708627d10cd4d04c245208c0000006a6999000000009600002b8000f5c0001148a17aa90000001c1e000403c000a4d30e7d38000c6090c80031092982afc8444043b2f4000019520000004b7b8a648900070222c082485f40d4001eb111a211ea9600031bd0e00010ce59bd8b324e25e8f05186fcac5dbcc598ba5443d0006e2522c9de2e618ca8b944e10d40f374e91040c76dec3a21078cd6c632fc54c5698cca2ad32263f902888c1bc17f856194eb7d32834f863354f1cc8894a5a2918498a300f4c8f1fc207c91c5f71388f941d88ce98198c2cbcd7a024850529700014308d245440188017a8706c0d860344665434564408aa800fe0801003890cb501e880ea18001850f141001347012242
def cut487k8p7 (i : Nat) : Nat := 0x21088
def cut487k8p72 (i : Nat) : Nat := 0x22281000430210962228100043021096222810004302109620a100840409110a109108001121041211104022021084c2222810004302109611104062021084c2109108001121041211105062061084c2222810004302109611104062021084c2109108001121041210910c001121041210910c0011210412222810004302109610910c001121041210910c001121041210910c005121041210910c001121041210910c001121041210910c001121041220a100c40419110a10910c001121041210910c001121041281104818041d019220a100840409110a20a100840409110a222810004302109642084408002a814e81104810001d0192
def word487r9 (i : Nat) : Nat := 0x1858289e64d08143e89c616919080fa271675461603c81e718580f9c89868094a72261854e03c81e71a802746534614f0272270201689e5827223a27023e4632b92c8136150842a0c03000ff50ffc43ff8cffd51ff507fd31ff487fd30ff443de33fd847fa00
def lay487r9 : Packing := (12,1,5,63,0,9,1,word487r9)
def keys487k10 (i : Nat) : Nat := 0x3580000000154a9800000000000000100000630000078400124001593755c0011512000d3e0e990028b329250000000000319f3000003d9c8000007103100381000000029100000002c70000000000000c2000e70000865
def word487r10 (i : Nat) : Nat := 0x20f1ff
def lay487r10 : Packing := (1,0,5,63,0,0,1,word487r10)
def samp487 : Array (Bits × Bits) := #[(0x226609003798001ea00cc0019007ff9c01ff,0x226609a4939d280ab51cea409a93538ea553),((~~~(0x3ff87dffb60001a73ff0fff91ff9ff1801ff : Bits)),(~~~(0x3ffd7df37f5791a73ce0f9bd1e69cd5b99cd : Bits))),(0x4784c0071e00061000ffff8fff800f80000,0x4284c60f1e308010c155868b618c2f984c2),(0x0,0x0),(0x0,0x0),(0x78070007e000381fff0001f000000ffffff,0x48070426c0210810860109d04408851188c),((~~~(0x7ff80007ffffc01ffffffe0000000ffffff : Bits)),(~~~(0x37ffedf4ffffac0bfdbffb68be9bd3ffafd7 : Bits))),((~~~(0x7ffffffffc000000001fffffffffffff : Bits)),(~~~(0x4a87f73fffb9c810c7558fff67ecffd9ecf : Bits))),((~~~(0x3ffffffffffffffffffffff : Bits)),0x37fd6df07f5780001c0038000e01c00381c0)]
def cols487 : IndexTree ColumnInfo := (.fork 11 (.fork 5 (.fork 2 (.leaf [(1,0,486,0,8),(2,0,485,0,8)]) (.leaf [(4,0,483,0,8),(128,0,359,0,8),(256,0,231,0,8)])) (.fork 3 (.leaf [(32,0,455,0,7),(64,0,423,0,7),(132,0,355,0,7)]) (.leaf [(258,0,229,0,7),(0,2,197,288,6),(0,4,291,192,6)]))) (.fork 5 (.fork 2 (.leaf [(0,128,323,36,6),(0,256,165,66,6)]) (.leaf [(3,0,484,0,5),(6,0,481,0,5),(32,2,197,256,5)])) (.fork 3 (.leaf [(32,128,323,4,5),(33,0,454,0,5),(34,0,453,0,5)]) (.leaf [(64,4,291,128,5),(64,256,165,2,5),(130,0,357,0,5)]))))
def lv487 : Nat → Packing
  | 6 => lay487r6
  | 7 => lay487r7
  | 8 => lay487r8
  | 9 => lay487r9
  | 10 => lay487r10
  | _ => emptyPacking
def ix487 : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 keys487k7
  | 8 => lookupWord 17 71 5 12 6 2 keys487k8
  | 9 => lookupWord 69 240 6 13 7 2 keys487k9
  | 10 => lookupWord 9 71 2 10 4 2 keys487k10
  | _ => fun _ => none
def g487 : Forest := ⟨487,10,fun j => samp487[j]?.getD (0,0),cols487,#[[],[33,101,135],[113,130],[129,114,101]],lv487,ix487,noFactory,noFactorySound 487⟩
def word491r9 (i : Nat) : Nat := 0xff
def lay491r9 : Packing := (1,0,0,63,0,0,1,word491r9)
def samp491 : Array (Bits × Bits) := #[(0x125982003b00c0049f4a001900ffe700ff,0x125983101b88e2048b4b20099064639091),((~~~(0x1f9e1bffb3ff0018e673ff91ff3fc600ff : Bits)),(~~~(0x1f9f5bcff3e7b998e6739fd1cf33d6cecf : Bits))),(0x0,0x0),(0x7e00018fff0007e1f0018fff003e0000,0x6a00128d0b0285a1f0248b1304be1414),(0x0,0x0),(0x3801801f000003801fffff000003fffff,0x80188be046118800108fd04a12944e4e),((~~~(0x3ffe001ffffffc001fffe0000003fffff : Bits)),(~~~(0x1bfff3d3ffebfac5abffb68bd374ffd7d7 : Bits))),((~~~(0x1fffffffffc0000001ffffffffffff : Bits)),(~~~(0x801ecfff67d9c800108fff4fd3ff4f4f : Bits))),((~~~(0x3fffffffffffffffffff : Bits)),0x1b9553c172e0b80000018000c03000c0c0)]
def cols491 : IndexTree ColumnInfo := (.leaf [(128,0,363,0,9)])
def lv491 : Nat → Packing
  | 9 => lay491r9
  | _ => emptyPacking
def ix491 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g491 : Forest := ⟨491,9,fun j => samp491[j]?.getD (0,0),cols491,#[[],[16,134]],lv491,ix491,noFactory,noFactorySound 491⟩
def word367r9 (i : Nat) : Nat := 0xff
def lay367r9 : Packing := (1,0,0,63,0,0,1,word367r9)
def samp367 : Array (Bits × Bits) := #[(0x90006ecb00cc0006a402403ff9ce700ff,0x941026cb42cd0802a50a509438c634243),(0x2000930c00fffc1b380380300e739ff00,0x2090030c0a542c0b384b84b12a5291312),((~~~(0x33ff31c0fff0ffd9c3ffc003ff07c1ffff : Bits)),(~~~(0x333c31c0f390ce5dc3ce50e33907c13535 : Bits))),(0xf03ffff000383fffc00000ffc00000,0x35035d07001a83ec1c01806ffc00a0a),(0x0,0x0),((~~~(0xfff003fffffffc03fffffffff00000000 : Bits)),(~~~(0xf6d027ff6bfdac0bfd6fd6f5bad6b5353 : Bits))),((~~~(0xffffffffffc00000000000ffffffff : Bits)),0x121c000001800615c10e10e23800003030),(0x0,0x0),((~~~(0x3fffffffffffffffffff : Bits)),(~~~(0x121f5035d1f547ffffcffcff3fffff3f3f : Bits)))]
def cols367 : IndexTree ColumnInfo := (.leaf [(4,0,363,0,9)])
def lv367 : Nat → Packing
  | 9 => lay367r9
  | _ => emptyPacking
def ix367 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g367 : Forest := ⟨367,9,fun j => samp367[j]?.getD (0,0),cols367,#[[]],lv367,ix367,noFactory,noFactorySound 367⟩
def word255r9 (i : Nat) : Nat := 0x1ff
def lay255r9 : Packing := (1,0,0,63,0,0,1,word255r9)
def samp255 : Array (Bits × Bits) := #[(0x90f051402b32b300cccc000406a493ea402403ff9ce739ce700ff,0x905051506b32b342cccd080002a4916a50a509438c6318c634243),(0x4ce2c0618033c33c00f0f000181b38e33380380300e739ce739ff00,0x4ce2c061b273c33ccaf0f328080b38e333b4bb4bd2a5294a529d3d2),(0x30a82003c03c000fffffe6263c0fc3c003ffc00f83e0f83e0000,0xa82017c03c00655541e2223c0b43c01ac1c06f83e0f83e0a0a),(0xfc0cfc003ffc0000ff00038383ff003fffc00000ffc00ffc00000,0xb40cfc117ffc0046ff011a8283ed003ed1c11846ffc00ffc04a4a),((~~~(0x70fff0ffffc0000000fffffc03fc00003fffffffff00000ffffffff : Bits)),(~~~(0x7afff0fff882a82ae0ffff8403fc00003ff27f27c900000ffffc5c5 : Bits))),((~~~(0xffff000003ffffffffffffc0003ffffffffffffff0000000000000 : Bits)),(~~~(0x6ffff079fa7fffffebffffac080bfffffff6ff6fdbad6b5ad6bd3d3 : Bits))),((~~~(0xffffffffffffffffffc000000000000000000fffffffffffff : Bits)),(~~~(0xb45fffd9ffffff67fffd9ea2a3edb57ed1ed1d47fffffffff4f4f : Bits))),((~~~(0x3fffffffffffffffffffffffffffffff : Bits)),0x6afff079f802a82ae0aaab800000000000300300c0000000000c0c0),(0x0,0x0)]
def cols255 : IndexTree ColumnInfo := (.leaf [(2,0,253,0,9)])
def lv255 : Nat → Packing
  | 9 => lay255r9
  | _ => emptyPacking
def ix255 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g255 : Forest := ⟨255,9,fun j => samp255[j]?.getD (0,0),cols255,#[[],[32,65,117]],lv255,ix255,noFactory,noFactorySound 255⟩
def word383r10 (i : Nat) : Nat := 0x1ff
def lay383r10 : Packing := (1,0,0,63,0,0,1,word383r10)
def samp383 : Array (Bits × Bits) := #[(0x900001baab2c02cb00cc000406a493ea402403ff9ce739ce700ff,0x9410009aab2d0acb42cd080002a4916a50a509438c6318c634243),(0x22000024ccc30030c00fffc181b38e33380380300e739ce739ff00,0x22090000ccc302b0c0a542c080b38e33384b84b12a5294a5291312),(0x10c00b338f0fc003f000f0026263c0fc3c003ffc00f83e0f83e0000,0x10cc3b338f0fc31bf0c6f31a2223c0b43c31af1cc6f83e0f83ecaca),(0xc3c0ff00003ffff00038383ff003fffc00000ffc00ffc00000,0x3c140ff0001b5d07001a8283ed003ec1c01806ffc00ffc00a0a),((~~~(0x1cfff03ff0000003fffffffc03fc00003fffffffff00000ffffffff : Bits)),(~~~(0x1cfe42bff0028b83ffe1ff8403fc00003ff27f27c900000ffffc5c5 : Bits))),((~~~(0x3fff0000ffffffffffffffc0003ffffffffffffff0000000000000 : Bits)),(~~~(0x3f6d0009ffffdafff6bfdac080bffffffd6fd6f5bad6b5ad6b5353 : Bits))),((~~~(0xffffffffffffffffffc000000000000000000fffffffffffff : Bits)),(~~~(0x18de3fffffffff9fffe7ff9ea2a3edb57ef1ef1dc7fffffffffcfcf : Bits))),(0x0,0x0),((~~~(0x3fffffffffffffffffffffffffffffff : Bits)),0x18de02abf0028b80a2e0ab800000000000300300c0000000000c0c0)]
def cols383 : IndexTree ColumnInfo := (.leaf [(4,0,379,0,10)])
def lv383 : Nat → Packing
  | 10 => lay383r10
  | _ => emptyPacking
def ix383 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g383 : Forest := ⟨383,10,fun j => samp383[j]?.getD (0,0),cols383,#[[],[16,66,134]],lv383,ix383,noFactory,noFactorySound 383⟩
def word495r7 (i : Nat) : Nat := 0x48f309183018b76cca86587550b17ad8950cb0eaa162f9b02a1961d542e83cccbab263ac896476cc855d6445caaa6d992abaae4a16d0d7568c7591222
def lay495r7 : Packing := (7,5,5,63,0,6,1,word495r7)
def keys495k8 (i : Nat) : Nat := 0x500a0d34804774016
def cut495k7p0 (i : Nat) : Nat := 0x80904000000000008090400000000000809040000000000080904
def cut495k7p4 (i : Nat) : Nat := 0x11104022021084c211104022021084c211104022021084de
def word495r8 (i : Nat) : Nat := (if i < 1 then 0x8595542aef2a27755142baf6987555142be768c7555142beb6887555142bed6847555142bee6807555142bbb698955c942bf368c955c942bf9684955c942bfa680955c942e7b615755c942afb2a2555c942f6b5d5545c942d5768e995d475b5768e995d475d1fa66665d475d4f650945d475d575d5931d565d5b5d5921d565e1f61c8799a55e4f9dd8421255e8f9998421255cdb6549560874d575d5931d564d575d5931d554d5e5d5901d554d4f9dc955d154d4fa667755054f0f9de6655054b4faa9751d644f0f999751d644d4f65c9795644d575d5931d644c5fa64855d572e4f2157591172d575d5931d552cdba20955c952d5b9dc955c952dcb256445c952d575d5931d542cdb2619295542e4f9dc8555142a7b2a1755c942d5b255755c9429eb2a5545c942b5baa9751d622d5b65c9795622dcb6509495622f4b9dd5415222f4b5d475912228fdaa99121576c7d9dd91215769dd684955d975ab768e889997587f6a2995d475a77aa97560c75e379997560c75cbba666660875a7baa97560875c7ba657560875e3b9997560875cbea666660075a7eaa97560075e3e9997560075a7b68a889dd65b5768c989de5599f2a666612559dbaa99221255d5b9dd9221255d9b9999221255a7768c989de558f768c989de559d768e995d65599faa9961d6559cfaa9941d655d8f999941d655d97999931d6559dbaa9921d655d9b999921d655d9d999911d655d9e999901d655add6868895574cbba666660874af368c9560874af96849560874afa6809560874cdba665560874e9b99a5560874a7e682889dd548ef6a29955054b6d684989de449ed684955da44d2f9dd9621644d6d9dd91216449e768e995d644da7999931d644d675d5931d6449ebaa9921d644dab999921d644d6b5d5921d644dad999911d6449eeaa9901d644dae999901d644d6e5d5901d644bce6809895644bce6808795644f0f9de6695644b8f6988595644bcd6848595644b8f6987595644bc768c7595644bcb6887595644bcd6847595644bce6807595644a7d684989de44c3f9dd9621644c7d9dd9121644ade6809895644c3f9dd9621572c6f9dd9421572c779dd93215728fdaa99121572c7d9dd9121572c7e9dd9021572b5768c855d572b5d684855d572ad768c855d572add684855d572ae768c8591172aed6848591172aee68085911728f768e9961d52b9b698955c952a3f69a889dd428bf2a1961d542a9f69a88955429f368c955c9429f9684955c9429fa680955c9429f368e995d622d735d5931d6229faaa9901d622d7a5d5901d622b9b6987595622bcb6907595622bd368c7595622bd96847595622bda6807595622bab6987591222be368c7591222be96847591222bea6807591222f4b9de5591222e179997560c75d475d5931d644a5768c855d572d535d5931d622 else (if i < 2 then 0x227c27626726125b25524f24924323d23723122b22521f21921320d2072011fb1f51e61d71c81b91aa19b18c17d16e15f15915314d14713812911a11410e0ff0cc0bd0a508d07506606005a05404e04804203c03603002a02401e01801200c006000cf729193a2175cf765993a2175cf765193a2175cf764d92a2175af768e8821175afb69a9960875afb6929960875afb6989460875afeaa99660075afeaa99460075cfe6599460075afeaa99260075afb68a889dd659f768e995d565afb68a885d565afb68a881d565cefa21941d565cf7a21931d565cfba21921d565dbb699921d565cfda21911d565cfea21901d5659f768e995d6558ff2a19759655cfb21d92212559fd684955d9748ffaa89859574afd6868895574afb6969960874afbaa89560874e7b69c9560874ebb6989560874eeb6909560874ef368c9560874ef96849560874efa6809560874afb2a655608748ff69699608749f768e995d564cf7a21931d564cfb2a1921d564cfba21921d564deb691921d564cfda21911d564cfe6a1901d564cfea21901d564dbe699901d564afe682889dd548ffaa8985d9549f768e995d554afe682885d554afe682881d554cbfa21961d554cf7a21931d554cf7619931d554cfba21921d554cfb619921d554deb691921d554cfda21911d554cfd619911d554cfea21901d554cfe619901d554bd768c7559554bdb6887559554bdd6847559554bde68075595548ff2a587955549f768e995d454cbf9dd9621644cfd9dd91216449f768e995d644cfb2a1921d644afe6809895644cfd2919121572cbfa219621572cbf6598521572cefa219421572cef6159421572cf7a219321572cf76159321572df36899321572cfda219121572cfd6159121572df96899121572cfea219021572cfe6159021572b3f698855d572b6f690855d572b7768c855d572b7d684855d572b7e680855d572abf6988561172af768c8561172afd6848561172afe6808561172af768c8521172afd6848521172afe6808521172af768c855d172afd684855d172afe680855d1728ffaa89855172cfb6889855172d7b5d59215172af768c8591172afd6848591172afe68085911728ff6969961d529f768e995d552cbfa21961d552cefa21941d552cf7a21931d552cfda21911d552cfea21901d5528ff2a587955528ffaa8985d152bbb698955c952beb690955c952bf368c955c952bf9684955c952bfa680955c952cfb260845c952b7b69c545c9528ff694989dd42abf69a889dd429f768e995d5428ffaa8985d542abf69a885d542abf69a881d5429bf2a1961d542cbfa21961d542cbf659851d542cf7a21931d542cf7615931d542cfda21911d542cfd615911d542cfe6a1901d542cfea21901d542cfe615901d542dfa689901d542cfb6889895542abf69a88955428ff2a5 else 0x7002e0040d002000000000000001a0040000000f00207001000000000000d0020617c816141c2f9020005002001c004003800c0000000000000000000000000001e005c00b8017002e005c00b8017002e004c008000006821d002a0040034008564de2f051e5d0022ac3c42ac3842ac385c004000000000000080000000000087c87687086a86485e85885284c84684083a83482e82882281c81681080a8047fe7f87f27ec7e67e07da7d47ce7c87c27bc7b67b07aa7a479e79879278c78678077a77476e76876275c75675074a74473e73873272c72672071a71470e7087026fc6f66f06ea6e46de6d86d26cc6c66c06ba6b46ae6a86a269c69669068a68467e67867266c66666065a65464e64864263c63663062a62461e61861260c6066005fa5f45ee5e85e25dc5d65d05ca5c45be5b85b25ac5a65a059a59458e58858257c57657056a56455e55855254c54654053a53452e52852251c51651050a5044fe4f84f24ec4e64e04da4d44ce4c84c24bc4b64b04aa4a449e49849248c48648047a47446e46846245c45645044a44443e43843242c42642041a41440e4084023fc3ed3de3d83c93c33bd3b73b13ab3a539f39939338d37e37837236c36636035134b33c33633032a32431e31831230c2fd2f72df2d02b82b22ac29d29729128))
def lay495r8 : Packing := (300,4,5,63,0,12,1,word495r8)
def keys495k9 (i : Nat) : Nat := 0x6a714b147812602944e1ca6956b3b84f4d20d64f10da178a1118b89b9e5c7c21703159138fc72f73b689120b000417199e000858e3a800002b42251829cfa64704a2f74a40e3e8f000204ec4a2148000000000b0a0c63652486010800194011f53ef8fa102c111928c4f0dc0000006b0ba2f239b2ebb479ab41d46b1a2edc10a300061c540608ac6b800055600034460f0c2010ed7a34924d22f0370f11c000000e54613465742410710be86a000b0030f641a8b600053e79b80006468ca888b71100020090aaae4b710a3c814ea490b7af05a6c59b82d8b19ba0000916c08c75cefd2f81cf5742c1c213bac00000074a4bfd4fe000c5a61bc1ec50fe7f243621522008200020d48ae41b4afdd97d1d2480c9cc36000000000306e00030780000012aa000695c00000095cd1d8000a23f4c800300f7230428002c9e00092b49f81900000002c55496e68e4888aa4a2000a02a300a0d433d8810ca59debee3ca34115e001b8d926adb1275d415b0f02e0f7a7c42ec9f5a548538003cd6097651000050109ee09f8b492c23f80f5a4c989687059badea18e84690dc27832cb8f1c1919506a619804407cf6e1ae8e7862d952f100aca3a008c53b83c1261fb65a73660231618d4c74783293ea25463a8c00827195666c4b9cdee968d2a5759a412c9313ec4dbe9224dcb788b7a22a72d2d45b2a06b5930a15b624e58a41c90e9f08679a4584396ec46942a495887716ff98f880067f4e8001ccd61ff462142d3092897ab98b477265e6318d25b43030e10a000a3c2131400c360eb01000000900000400f020ca8d00341021a0c100107401202100040ae408300055aa540c18000044851a1410208341840000a81540008004103801ba87031804006a05d48060043a4000488e
def cut495k8p0 (i : Nat) : Nat := 0x80904000000000008090400000000000809040000000000080904
def cut495k8p107 (i : Nat) : Nat := 0x8090400000000000809040000000000080904000000000008088400000000000c0b0400000000000c0b040000000000000500000000000000098400000000000009840000000000002904000000000008090400000000000921900000000000092190000000000002108800000000000210880000000000021088000000000008090400000000000809040000000000000500000000000008090400000000000809040000000000080904000000000008211000000000000029040000000000002904000000000000290400000000000809040000000000000110000000000002108800000000000c02100000000000080904000000000000288400000000000809040000000000000500000000000000098400000000000210880000000000080904
def cut495k8p144 (i : Nat) : Nat := 0x10910800116104121092080011410412109208001141061211104022021084c211104022021084c211104022021084e2109108001161041210920800114104121092080011410612111040220210850211104022021084c211104022021084c211104022021084c211104022021084c211104022021084e211104022021085021091080051210412109208001141041610920800114104121092080011410412109208001141041210920800114105d21110402202108502111040220210850211104022021084c211104022021086021110402202108482111040220210848211104022021084a211104022021084c211104022021084c2111040a2021085021110402202108502109108001121041211104022021085021110402202108502111040220210850210910800112104161110402202108502111040a20210850211104022021084c2111040a2021084c211104022021084c2111040a2021084c210910c00112105d211104022021084de111040a2021084de10c080c208288882109108001101041210910800112104161091080011210416811201100214218e10c080c2082889c610c080c2082889c610c080c2082889c610c080c2082889e210c080c2082889c21092080011410412109108001161040e109208001141040e109208001141060e111040a2021084c21091080011210412424088420c008946
def cut495k8p208 (i : Nat) : Nat := 0x11104022021084c211104022021084c211104022021084c211104022021084c211104022021086021110402202108482111040220210848211104022021084a211104022021084c21110402202108502109108001121041211104022021084c211104022021084c211104022021084c2111050220610860211104022021084c211104022061084de11104022021084de20a100840409110611104002021084e21110402202108502114220002104085a11104002021084e211104002021084e2111040220210850211104022021084c211105022021084c211104022021084c211105022021084c210c080c20828898611104022021084c211105022021084c211104022021084de11105022021084de1142200021440856811201100214214a811201100214214a811201100214214a10910800112104161091080011210412111040220210850211104022020084c2242100840401110a11104022021084c2109108000121061210920800114104121110402202108502111040220210850211104022021085c211104022021085c211104022021084c211104022021084c2111040220210848211104022021084c211104022021084c2111040220210848211104022021084de11104022021084de1110402202108502111040220210860211104022021084c211104022021084c211104022021084e21092080011410416
def cut495k8p272 (i : Nat) : Nat := 0x1091080011210412109108001121041210910800112104121091080011210412109108001121041211104022021084c211104022021084c211104022021084c211104022021084de11104022021084de10910c001121061211104022021084de1091080011010412114220002104085a1091081019010412109108001101041210910800112104121091080011210412109108001121041211104022021084c2109108001121041210910800112105d21091080011210412111040220210850210910800110104121091080011210412111040220210850220a1008404091106
def word495r9 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0xecb10ab96df614855caf7b2842ae57dd9321572bfac890ab95fe640855cabfd32baae59fe885d572ebe42aeab96df215755cb6f9312aae5b7e8895572ebe4bcaab975f9de555ca7f9312aae5d7d7595572ddec2108b94ff261545ca7fb302a2e55fd9715172bf6c90a8b96efa22445cbb7cef222e5bbc8591172edebac88b97cf956445ca7fb2f442a5bed92a21529ff4cb0ea967f61c8754b3f9313baa59fe889dd529fe4c4eea967f61e7754adfb2c3aaa57bd941d552beec98eaa95fd6447554aff3203aaa5b7d8795552ebf3bcaaa96ef6108454a7f930ba2a53fd981d152bf6c90e8a96efa224454b77b0f222a5dbe7791152f9f2ac88a95fba657254afd930b92a5bee885c952ef643ae4a977b9dd7254bed92ab92a5ded755c952fb72aae4a97eb9117254a7fb2f442853fd95a2142cfe4c4eea167fa227750a7f9313ba859fd879dd42cff3bb0aa14ff65c8550b3fcee42a853fc985d542b7ecb0eaa15f764c7550afdb243aa857f5911d542bfcc80eaa16df2625550b6fd112aa85b7d8795542ebf3bcaaa17cf2525550bedb252aa853fc9895542dbec2caaa15fb64a5550bb7ceeaa285f3e5555142edf3bc88a16ef2164450be7cab222857ee995c942df7442e4a177b21d7250bbdceeb92857ec955c942df6c2ae4a177b5d57250bedcaab9285fac945c942fd6aa2e4a17eb9117250bbd92b3bc45dec949de22bf64acef115fba657588bbdceebac45ded751d622fb6cbcab117db25e5588bedcef2ac45f6d9495622fb64a4ab115fb65e5588bbdcef2ac45f6d7595622fb63acab1177b9dd7488afd92aba445f6e555d222bf6ca8e9117db9547488bbdceeaa445f6e5555222bf6cb8a91177b9dc5488bedcaa2a445fad5415222fd73bc89117eb5d64488bf58eb22445fae5591222ef73bc89117db9564488aafd32ba8ebc7e665d475cbec390f2aecf61084956e792aba2a973e9955054e9f3baa82a78f99954153a7aea3ac8997c855d572bb64aae4a96cf2155450badaea3ac45f2d54152229fac890abb4f764e885d65fd32c30eb3be9961075d5f333083aeb7999831d73baeac18eb3ee9960875d77333043ae7b5d5821d75ecccc08eb3fa9960075d7d333003ae7e5d5801d67db25442cbc7e7799a55bb6c91092ad9f65875956e7b283acab75d931d655bb6c90eb2addd64475956ef3203acab3f591a21749f74cb043a6bb999821d36dcaac10e93f990a2154bdcc810f2272f9de66912d7b2c42c897b59121644b5ecb0eb225e764c75912f5b243ac897b5911d644bdcc80eb2274f9de55913c7ccd2ac892fd96216449fac890b224bf658855ca77b2842ae53dd93215729fac890ab94fe640855ca5fb2d442856ed961d622bd6ca0eb115f364c7588afcb223ac457e9901d622eb73bcab1176b9de4488be5cab2244595d7560c75 else (if i < 2 then 0x44ccbaf3f9de665d777b08422eb5fe995d475e7f332ea3aefba65821d77db2cc10ebbed9460875df64a3043acffa65821d73faeac10ebbf99660075dfcca3003aefe649801d67fb2f442cb7f99021d65cfe4c4eeb2e7fa22775967f9313bacb9fd879dd65e7f3baecb2def65075596fbb263aacb7ed921d565bfac88eab2dfe64075596efb2c43cab77d9421e55bbec910f2af5f26277957af9293bcabd7d879de55ebf3bb0d2addfa6576956ef930bb4abd7e775da55f3ec3ccd2af9f21e66957cfcef334abd7e7761255f3f333092addf65c84957afcee424ab77d9621255f3f331092addf64884957afceec14ab77d9521e55cfe4c4ef2af5f256779567f9313bcab9fd879de55cff3bb0d2acff261769575fb0f334abcfe7799a55bbf4caeb2af5f9dd75957cfcccbacab77d961d655f3f330eb2addf65075956efb243acab77d9759655ebf3bacb2af9f5d9659573fceec24ab77d9521255bf6c91092ae7f9dd829567fb2b442e9cfe7799974cff3b90aba6bf998855d27fb2442ae9b7c855d5749fe4c2caba6df262555d36fd112aae9d7e7795574ebebb4aaba79f99a555d3e79292aae93fc98955749ff4cb0a3a6bf999851d36fb0d2a8e9e7e6695474dbec2caa3a6fba65821d37db2ac10e9bec9560874df72ab043a4ffa65821d36fcaac10e99fc989dd64cff444eeb267f61e775927fb2e42ac99fe7721564beec98eab25fb64875592feb223aac97f9901d564dbe4c4aab26dfa22555936fb0f2aac9d7e77955649fecbd10aa5fb648875533f9313baa99fe889dd54ede4a4eeaa4ff262775533fb0f3baa99fe77619549fe4c2ecaa73f9de66552dfb2c3aaa97dd931d554bf6c90eaaa5fd64475552ff3203aaa9d7e7759554dbec3caaaa75f9de555536fb0d2aaa9e7e6695554edf3bae8aa7cf955745527fd32c38a99fd879dc54cff3bb0c2a6bf61e661539fcef330a9b7d8795454ebf3bcaa2a6df61a55153cfccd2a8a97be9955054ddec3aa82a76f9dd54153d7cccaa0a93fe9960854cff3bb042a6df9558215377aa8c10a97bd9521e44ede4c4ef2276f25677912f792b3bc89dbe775da44bde4aaed227af9de66912f7b2e42c89dbe7721644bdf4caeb2276f9dd75913d7cccbac89ebe661d644edeba8eb225ef64875913b7ceeb2c89f3c9895644f9ecbcab227cf25e55913e790f2ac89f3e7795644f9ecb4ab227cf5da55913e7b252ac897bd9795644edf3bcab227af99a55913e790b2ac89f3d7595644f9e3acab227cf59655912f7b252ac899fc989de44e7f3bccd224ff65c859133fcee42c897dd931d644bf6c90eb225fd64475912ff3203ac89b7c9895644ebf3bcab2279f99a55913e7b292ac89dbe775d244bde4aae9227cf95574913b7ceeb2489f3e5559244edf3baa9227cf955549127fb2b442e59fe7721572b7 else 0x92aeff21c84956ffb2c424ab7fd9221255dff3bb052adff255765d37faec42ae97fe9921574bfe4c4aaba6ff262555d37fd112aae9dfd7695574fde4a4aaba5ff64a555d37fd32c28e9bfd9261474dfec34aa3a6ff616551d2ffb252a8e9bfc9560874dff2ab043a6ffa2277592ff92b3bac9bfe7721564bff4caeab26ff261755937fd10baac9bfe881d564dfe4c4aab26ffa2255592ffb2f2aac9bfd8795564bfe4c4eeaa6ffa22775537fceec32a97fe995d554dff442eaaa6ff619755537fd103aaa9bfd861d554bfec90eaaa7df9dd65553efaeab2aa9f7c7559554dfec3caaaa6ff61a55553efacb2aaa9fbd755d154fdf2aae8aa6ff9dd86152ffd32ba8a9bfd865d454dfe4bb042a6ff9dd821537faeac10a97fc959de44dff3b90b225ffa65759137f930bac897fd921d644dfe4c4ab225ff65e55912ffb252ac89bfd95a2172dfeca510b95ff656885caffd3242ae5bfe8821572f7ecb10ab96ff614855cbf7b2842ae5fdd9321572ff6c910ab97fd644855cbff32042ae5dfc855d572efe4a2eab95ff262555cb7f9312aae5bfe8895572efe4bcaab977f5d6555caff92ac22e5bfc8561172dff44108b95ff654845cb7fb0a422e5bfc8521172efeba908b95ff255745cb7f90aba2e57fc9855172dff442a8b977f5d5545cb7fd102a2e5dfd7515172dff44488b96ff216445cbbfaeb222e5bfd97a2152dfeca510a95ff65e8854b7f928c3aa5bfe8821d52bfe4c4eea96ffa227754affd32baaa5bfe885d552dff440eaa96ff61e5554b7f90ec22a5bfe8821152bfecb908a96ff61c8454b7f90e422a57fc985d152dff442e8a96ffa207454affb2a3a2a5bfe8855152dfec3aa8a96ffa205454affb2e2a2a5bfd8715152dff44488a96ff61e4454bfd92ab92a5fed755c952ff72aae4a97fb2517254bfd908b92a5fed745c952ff6aa2e4a97fb1517254bfdc88b92a57fd9521d42bfe4c4eea16ffa227750aff92b3ba85bfe7761542dff3b90aa15ffa648550affb2e42a85bfc8721542bff4caeaa15ff2617550b7f930baa85bfe885d542dfec2aeaa16ffa207550b7fb0a3aa857fc9895542dfe4c4aaa16ffa225550affb2f2aa85bfd8795542dfec2caaa17ef2525550bf7ceeaa285fbd7555142fde3aaa8a17ef9555450bfd92ab9285fec855c942ff6baae4a17fb9557250bafd32ba8ebd7d965d475ebeca2ea3af5f251751d7afb24ba8ebd7d751d565ebeba8eab275f5d475553e792eaa0a9f3e7755054f9ebaaa82a75f5d475913e7aa82a2e5d7d751d552f9eaa0a8a975f5d47550abfb2c42cef5fd9421677afec910b3bd7f658849debfb2a424ef5fd92212779fec910b3bcff656885db3fcee42aed7f59121576e7e4acef3373f2527799adf92b3bccd9fd97a2175deec9d10bacff64a885d6fbb27442eb77c955d975d7f4)) else (if i < 4 then 0x9abe52f8ebe22f82bdf2f76bdc2f6abd92f5ebd62f52bd32f46bd02f3abcd2f2ebca2f22bc72f16bc42f0abc12efebbe2ef2bbb2ee6bb82edabb52ecebb22ec2baf2eb6bac2eaaba92e9eba62e92ba32e86ba02e7ab9d2e6eb9a2e62b972e56b942e4ab912e3eb8e2e32b8b2e26b882e1ab852e0eb822e02b7f2df6b7c2deab792ddeb762dd2b732db6b6a2d9ab632d7eb5c2d3ab3d2cdeb2c2ca2b252c86b1c2c4ab052bd6af22bbaaeb2ba6ae82b9aad52b1eab82ab2a9b2a5ea8a29f2a6f297ea542942a4d28f6a3628c2a23285ea0a27fa9f127b69e827929e127769dc27629d527469d0273a9cd272e9c6270a9bf26f69ba26e29b526c69ac26a29a72656992263a97f25ee97a25da97125b696a259a963257e958255294f251e94424e2935247e91c245a913240e90023ca8ef23ae8e8238a8df236e8c622ca8af22ae8aa229a8992226878219a857214e850213284720de83420a281920368021ffa7fb1fd67f21f8a7d91f567d21f3a7bb1ec67aa1e727991e1e77a1daa75b1d367461cf27391cc672e1ca27231c3670a1c1a7031c066fe1bf26f91bde6f61bca6f11bbe6de1b6a6d71b4e6d01b3a6cb1b1e6c61b026bf1aee6b81ad26b11ab66a81a9a6a31a7e69c1a6a6991a566941a4268d1a266861a126831a0667e19ea67719ce67019ba65f196e64c18f262d187661a1862617184660e182a607181660418025fb17a65e417625d517265c016da5ad16a65a4168a59f166e598164a591160657c15ea569156654a14ea53714d652c149a523144e51014024fd13e64f613a24e313564c812f24af128649c126a497122647a11a2465117e45c116a4551126446111243f10f643210b2427105e40810124010fce3ec0f923d50f3e3c20ed23a90e6638e0e0a37d0de63720dba36b0d8e3520d2a3430cf63380cd23310cb63260c8a31f0c5e30a0bfa2f30bae2ea0b722d50b462ce0b2a2c70b0e2c20b022bf0af62b80ad22b10abe2ac0aa22a50a8629e0a6a2970a4e2900a3228b0a262880a1a28309f627c09ea27909de27609d227309c627009ba26d09ae26a09a22670996264095224508de22a0872213081e1fe07d21e9077e1d607321c306d61ac068a199063e18805fa17705b615c054214504e612c047a11504260fe03ca0eb03860da034a0cb03060b40292095021607a01b2061014e04800ea031009e01e005200b00060002ffd3242aedff59121576dfecb510baeff652885d77fb25442eb7fd96a2175bfeca510badff64a885d77fd10422eb7fd9621175bfec9108baeff211825d77f928c10eb7fc989dd65dff444eeb2dffa65755977fd10baacbefd765d565dff440eab2dff65887956ffb2843cab7fd9221e55dff3bb0d2adffa6576956ff930bb4abbfc985da55bff4caeb2adff65d65957dfaecb2cabbfe7761255bfecb9 else (if i < 5 then 0x30f0b045b147e08400191842a107001a10400280105a008402018178b87831e806608857838b851e5c307804f8b871e562e0e1c79187838b1e460e2e1c79182183600a0c387801c3050f8020038201787838b1e7a0430800a0605c7e2e1e013a020140804031c3870a0625e0e2e1c79c281b838b84951e7c30404643a01592810e2c304141008040018407430440231f8b87803a7c307801c3042387838b1c40642a00b149b878b811e61326e1e2e0c79b1787831cb25c52661e2e0c79b149b845b8b1e642a0080c30418178b87831e60605020100c70e1c281b0b07011c14388c3050a802c304086600b8b87821c3a56084006608a0e006e1e2879582182608688281008040098407100608e2e1e0c79f801a0842823838b871e64441a00e1201803050201000ac7101e0d8220a06e2e1e0c798289b8b87805260ae1e02cc7942b0b0700191c3a70ae2e02bc794589b8b871e545e08a8214441a00f101e005171382310060508e1e2e0c7a1128100305472a0d820e260830b101a00710186c4600d8018706171180315e2e1e0872a9b8b8019221e506e0e1e28797118218300ab8b87821d226c460860c9812607001c0868818208006461890e1c004062050e1a1044c1a1070018306821a0070018000006284950e2000000000000000000000000025437182b8b831e76210c60fe7e1e09c54521b8b87826181386e2e1e098619e1b8b8782667e1e08c93938780302a586e2e1e0921b8b87824e4e0e10ae2959f8b822e486e2e116919e1b8b864e4e1e2169310578b8780526a7e2e1e090978b8782426e2e1e0909b8b87824e1e02c8f8b87809a4e2e02b8c5b8b849a4c6181310e7e2e012a21a178b878258685e2e1e0961a178b878251813e7e2e11198604c449b8b866a7e2e1e090544f8b87825181312e2e094549b8b87825e1e02c8c9b8b87824e2e02b8c9b8b863e2e1e08d9f8b878240a09e2e1e01398604c2b9f8b804a7c60ae2e1e0c3159f1828238b87831e7c6e1e017c79437182b8b831e6c6e2e116c79424238b87811e61426e2e1e0944f1c9b8b87826c7e1e02c931f8b80ae4c726e2e1931f8b87824c7e2e1e0931f8b87824032becae32b2cab32a6ca8329aca5328eca23282c9f3276c9c326ac99325ec963252c933246c90323ac8d322ec8a3222c873216c84320ac8131fec7e31f2c7b31e6c7831dac7531cec7231c2c6f31b6c6c31aac69319ec663192c633186c60317ac5d316ec5a3162c573156c54314ac51313ec4e3132c4b3126c48311ac45310ec423102c3f30f6c3c30eac3930dec3630d2c3330c6c3030bac2d30aec2a30a2c273096c24308ac21307ec1e3072c1b3066c18305ac15304ec123042c0f3036c0c302ac09301ec063012c033006c002ffabfd2feebfa2fe2bf72fd6bf42fcabf12fbebee2fb2beb2fa6be82f else 0x8f802e007801e007801e004140804019c38610080605e2e1e0c7a019822e261e0c795149812607001e0460b1b878042405020100670e1b1b938f818b84427a486821c20608200a06656423e2e1e0a1958985809c3a6066261608a640e9f8b87808d9650a080605e2e1e0a7228c165e186e2166799918e1b885b8666586e2e1671698140c08040018407e2e160c79517801a084201427838b871c74342a00c198022618e2e1e0c79b178780b31e5c526e2e1e0479b178b80af1e5c52616e2e1c79b80121e00b801268498102901a407801020800a4a18a861e0060e0060e0068c122e00b821003824238b8780984282605801080509e0e2e1a71e8010302106a20a881c004921c0070012322c00e8c1c0260a1205803e007938b87822a56004382418100c438b878022ac10419822180418140804019c3870604638b87829c566e006821c10681102c1078010e0906040305e108e2e0283824100e1b8b878214960068018280115e2e1e0230e981991898582543a70685e4e2e1e01523a05439921a178b878280a0605e2e1e0a79d801e00710141a00820140804031c40760042b8780b31e50e0ac426e2e1e09c2b8b831cae51626e2e1c797801c40506802c404100c08040018407e2e1e09893801a0878010e09080403e0e2e126250906810048380600c638b87829c566c08429130ca49b8b878280ac4c3e12ce0983b110c9b8b878270ac4c326e261e09f130c9b8b845a68560840d090681004c0050e81003c0041982260860838242018100f8b878214aa005801a0060a0040a00408028100010080605e2e1e0a72180160068c1e00602607001009b022038018587021a2068a185248a0c0068c145860811610190164058c1c004002062051616307001e08400403020005e1101d8210ac4c3c1c00cc59c281b130b07031670ac4c3c2c00bc51c1b1)))
def lay495r9 : Packing := (630,3,5,63,0,14,1,word495r9)
def keys495k10 (i : Nat) : Nat := (if i < 1 then 0xe423000000044d80198554000d5a096164f7c2e558adb1000007973a9d7b0000000c7e3d3a48ca842117654347f727446a0000e00c000734960510ffc25871e5a2519710ca9c320b85bf0662798000d2b50a204690a725dd23747164e630add9b08c615e80784d7485941198e6529091a90e718400067ed24af29756aa790000961c1aa00035d60003837611ee6bc75f0c60002956831520a966be3485bbe1116dc000934d991c134c48a46d9e006000c186ee58c548b8f10000deb0000000000188338a29940000000d248000f056d1e76b6a2994cc0000001c4bb6f7247b0ced5ac7310021635cc90001478921f531b2028e872e4db2d8bc0000839c12610564d536ba2e68418542941966662ad149968cfde3e942f31f566cc405a72d46617db0364c324596757072127599d95df31106d249b47a25f800015b18dcb74ae3dc71090603ca22af07c000a5f000048534bd52fc000d7891c903501690000868000056de40b428c02c000f906c7e0002ddf00011971743235392d5f12400000a0e651c000053c379c0002032e2491898f7760ac590001d54000000021ac00011d0c8bf24d98e98cf44376becbe0003973c55c000f27603c660ed1f00015d423fb9e932f0a540000000536c000000103000005cd24ec000238ad05f33800000000000001e27a6e2951c0165a30001cf856999a14775c3447e818525e565ee5131ec6270000b886df763d9198930219d0001c08306a612016d21ea75652b153210f64fdd4297f80000002ddbc1684f500024b200028260000000b95800054f921dc81284e79c70ec35d0c3d0000a1c93a7c221970e57428c8f3d1025e13720886f8e81bed41d0e3a9a649ad1ca0a042448fb82a49284331c6458ef999b67d050000218fb1f2c8cb2080009916d76a5c4da939091cea6e8457d37909e04bc48a28300004159cd6e02400000034a1f25c85f000244403b9e1a672a534a90c000000089be975d40a56361bb694cb486fd1849385c3bd03ea090000cc2005c0003899c600000000a8341da042e000f484125067010345254e46028636b9811a0f155414246392077db9b619bc603280897a996c4b8374f89506d1a1787d5871e26695941fc20812d4648825886391be82df4c9d30409c992e58c9b9a14ad24b5ffe7344abc75c5e1d1361240151c000078000f123a44b1c004c00c081811200000881600180003458026303b524002897a20001168c0020e1d382001c90f144458404002800201304000849b0200021042082900f470611001050a280004801481090420e0400c06040841d000831200d84800e04900000000a60000020000fa200000070000500020c120000440548480000004010000509a0a0012d26dab00000462002507004a141060c0c08136048891a0000d003630600488941644005044400d else 0x1575957ed64594adc137ba48dc170a22d926db002a1a19937fcffa455dcb393b0cac3410a40001085d8b00ae84250b0953a1886580000e1c28eb00e29e5e423a1f52eec4f733d945c626cd9453d8af0001263173d0ddb64d89fc8825045658a4c244183500000000003cef0001186a4d400007672137894000f9854812992523f54ddc647abd72e77b9f90596494719e1fc531e458252101005af1a7b8c0000c570000811ac060000000014c66e34df47b00028f900021aee09160182cfc2c5298651d51b01d8061e6d562c000c45ddbc000000087cb24f76d7defb2d95f013368e55347c8f00004510003200774600ec8f9112a081e0f70868ed4011801c8561e3b1de141e17b10dc262088f4e58d840c704506570c8039e86c82e8c7387d3238388c97017cf9ff63f21d894e14f0d81bcab3771490b59d65f86058b7f94ddabf22495bf12aa58c528cacd6791c361a5d4df1bb5e85212644a1db52e238052d298a90ad13342af99948eb0ebcd568b522bf51f4131548000f0fb19073d2255806da400000a07405a83268fcd2c40a6d11f6cc66839ab66506b054bc1a9a59e2c5c3628609a4a32dcaa000151dc54000077005ed0000a3c3708000c01)
def cut495k9p0 (i : Nat) : Nat := 0x80904
def cut495k9p56 (i : Nat) : Nat := 0x809040000000000080904000000000000050000000000000009840000000000021088000000000002108800000000000210880000000000021088000000000008090400000000000809040000000000002904000000000002108800000000000809040000000000021088
def cut495k9p418 (i : Nat) : Nat := 0x80904000000000008090400000000000809040000000000080904000000000008090400000000000c0b040000000000080904000000000009219000000000000210880000000000021088000000000009050000000000000809040000000000021088000000000008211000000000000121100000000000080904
def cut495k9p434 (i : Nat) : Nat := 0x1110402202108502109208001141041611104022021085021092080011410416109108005121041620a120840c09114a10920800114104161091080051210416111040a20210850210920800114104161110402202108502111040220210850211104022021085021110402202108502109208001141041610920800114104161110402202108502114220002144085e222818004302109a10920800114104161110402202108502111040220210850220a100840409114a111040220210850211104022021084c211104022021084c2109108005121041211104022021084c211104022021084c21091080051210412222818004302121611104022021084c211104022021084c210910810592104161091080011210416111040220210850210c080c208288906111040a20210850211104022021085021091080011210416109108001921041611104022021085021091080011210416109108001921041611104022021085021110402202108502111040a2021085021110402202108502111040a2021085021091080011210416109108001121041610910800112104161091080011210416109108001121041610910800512104161091080011210412811201100214218e10c080c208288a0610c080c208288a0610c080c208288a061092080011410412109208001141041210910810190104121091080011210412
def cut495k9p498 (i : Nat) : Nat := 0x11104022021085021110502202108502224205040921214e811201100214218e115020042304085a811201100214218e1091081011210416109108081121041620c211040c0921ce222810004302109610a13002082a81d61110402202108502109108001121041611104022021085021110402202108502111040220210850211104022021085021110402202108502111040220210850220a100840409114a11104022021085021110402202108502109108001121041620a100840409114a42084408002a81921110402202108502111040220210850211104022021085021110402202108502111040220210850211104022021085021110402202108502111040220210864211104022021084c211104022021084c211104022021084c211104022021084e611104022021085021110402202108502111040220210850210910800112104161092080011410416109108001121041610910810192104161110402202108502109208001141041611104022021085021110402202108502111040220210850211104022021085021110402202108502111040220210850210920800114104161110402202108502222810004302109a114220006164086611104022021085021110402202108502111040220210850211104022021085021110402202108502109208001141041610920800114104161091080059210416
def cut495k9p562 (i : Nat) : Nat := 0x1091080011210416111040220610850210910810192104161091081019210416109108001121041611104022021085021110402202108502111040220210850211104022021085021110402202108502109108001121041620c211040c09214e10910810192104161110402202108502109108001121041610910800112104161091080011210416109108001121041611104022061085021091080011210416109108001121041611104022021085021091080011210416109108081921041642086408082a82121091080011210416109108001121041610910800112104161091080011210416109108001121041610910800112104161091080011210416111040220210850210910800112104161091080011210416109108001121041620a100840409114a10910800112104161091080011210412109108001121041642084408002a81921110402202108502109108001121041642084408002a81921091080011210416111040220210850210910800112104161110402202108502111050220610850211104022021085021091080011210416111040220210850211104022021085021110402202108502109108001121041642084408002a819210910800112104161091080011210416222810004302109a11104022021085021110502202108502224205040921214e11104022021085021110502202108502
def cut495k9p626 (i : Nat) : Nat := 0x111040220210850211104022021084c210910800112104161091080011210416
def word495r10 (i : Nat) : Nat := (if i < 1 then 0x55f577c81ee97ae5e82792de1b7775d9f75a1d2373b1cc37215c4e7041be06ea5b726d09b126b35a966929a1367a99ac65d594564018d06211846603d7d85ea177f5d217035b696aa59e963c57f95d5567956754dd4f95341499516d4244fb53b64de134f4c452d34a7125e489d1f7471d17b44f50ff433d09841a102a3fe8fbc3e4cf633cccf033b30e953994e3537f8db935ecd363434ccf3298c7d3150c162f7cba12de0b482c28ada2aa8a6528b89fe2738997259c93724008bb222c84d20747ed1ef477f1d047111b686a3199463c17f85d5169456e14f850e135c48b116c4240fd03bd0e3435d0cb43040b502ce0b2029f09a023108201d806bc186057413b04100d4029007b01480300003ff21576ffe885d7ff61975ffd765d7ff61175ffc845d7ff60975ffc87597ff9dd65ffd75597ff1d565ffc87957ff9de55ffd76957ff5d655ffd65957ff21255ffd765d3ff21574ffd755d3ff59574ffe555d3ff95474ffe77593ff5d564ffc75593ff95564ffc87553ff9dd54ffd76553ff5d554ffc75553ff59554ffe55553ff9dc54ffd75153ff9de44ffd75913ff1d644ffe55913ffa2172ffd855cbff21572ffd755cbff95572ffd845cbff21172ffd745cbff55172ffc545cbff91172ffe8854bff61d52ffc8754bff9dd52ffd7554bff1d552ffe5554bff61152ffc8454bff5d152ffc7454bff55152ffc5454bff91152ffc8750bff9dd42ffc8550bff5d542ffc7550bff95542dfc859df7f21277bfc859deffa2176dfe775daff21576efe7799affa2175dfe775d7bf99975bfd861d7bf99875dfd751d6ff61075bfd821d6ffa2165bfd875977f9dd65efd76597df61e55f7c87957df9de55f7d86957df5da55f7d84957df21255f7d82956ff61e55dfe77956ff61a55efe66957df5d655f7c75957df59655bfd84956ff60a55bfe885d37f9dd74dfd765d3bf99974bfc855d3df95574bfd861d3bf99874bfd851d3df95474bfd821d2ffa2164bfd875937f9dd64bfc85593df95564bfe88552ff61d54dfe77552ff61954efe66553df59554f7e55553ef5d154bfd871537f9dc54bfd86153bf99854f7e55153ef55054bfd82153ef21e44fbe77913ef5da44fbc85913ef5d644fbc75913ef59644fbe559137f9de44efe66912ff21644f7e55913ef5d244fbd64913ef55244bfe885cb7f9dd72bfc855cb7f5d572f7e555cbef91172bfe8854aff61d52dfe7754bdf95552fbe4454bfb5c952bfe8850aff61d42dfe7750aff61542bfc8550bdf95542fbd5450bef91142fed7250bfb9de22fed7588bfb1d622fee5588bfb5d222fec7488bfb55222fec5488bfb91222d7d751d7cf55054cfe7799abf61875bbd841d6f760c75bed821d6fd60475bf9801d75f9de55e7e66956fb60874dbe77913af99a44f3e559137b9de22f6e5588beb91222 else (if i < 2 then 0x9a78c9a2a5c38b00a8f4a64b8b0e08e3a7c38b0258f290141b147c3809d0392e1c5823a69e3260b8b0e08e4e88d871608e9668d863e2c0949ce17161c0213479c2e2c3823a699362c380447985060a40461c18a3d228462c3823a69d5464c2028ac587047a92a4461b062c3386c18b0a5944880d9f062c22a8211b161c11cacf14360c5863cc544068d8b0e0151e94b8b0e08e9a61424405211b3e1c18aa8b1218a0d87062a0c468b87027c538a0d8b0e04e567318b0e04f1a6c9870621528a0c63161c04e7101470a0d8b0e04f4e2c38239595361c18a39598345c587047985260d8b0e00e5684c95223c58700aa0561c58134a95223c5870269d325c5870271538a4b831614f3264a8d262c1845502b0e2c09654c97161c0293ce98290c19f161154454d931e2c38270c2b161c09cace62345c5870279c525488d361c18a8158b0e04d29814992e2c3813d01820a278b061314060b8b0e0149e72016313c587018a22430d17160c33e2c3813982b3464f8b061313090c16308cf8b0e01550a8d16243c5830d028305c5870094f446c5870278b305ce54362c3827151b161c11661438305c587027a0462c3823999880a4d8b061111e80d8b0e08f28a8f8b0e03330a8d8b0e08f305278b0e0313104c63161c04e70d16243c58704e1b161c0213cd193e2c380c4c17161c09cc159ca8a8d121c5c58705229306278b0e0314060a288672b8b0e0a4362c3822ca18505c5870094f462c3813c594562c3822ca570e2c02a50c38505c587027a13130b8b0e0313888a911e2c3813518b0e04e5652617161c062610992232b87062a0a85c58702699362c38139598a884d17263c5870529a243c5870459d3e2c38229898513c5870189a344878b0e08b385278b06131327c587008333260a63161c04e714202c621831618f4c50d831618f3080d1b161c11c55028860c38a3cc2a2e0c5863cc202e0c5863cc203051d871608f4080a98861c18a3d01a2e1c5823cc2a345c38b0479c4460b871608f38a0c98761c1883d18b0e0111e52029360c584447a0362c3823ca1b0e2c0223cd14462c3805479c546c58704798562c3804479a305c5870088f3868a382a691831610f525c5870474d3134c970e08f8a7278b0e08e9a626992e2c3823ce9b147c1849cc9b161c11d2cc9b147c3809cd8b0e08e9658f8b0e04a4e60004d8b0e08f28ac618ae2c38271420367c58704e2b3e1c03251590362c3826159f160172960d9f16195367c58704b8b0e04f215c8182e2c38274d173e2c38263117161c09e68b9f161c12a6c58704797161c11e42697161c11e6ae9eb69accaaedaadaa71a906a11a74e995a55e920a336881a0ba7e99eca76d9cda6dc9a7a63d97e25c8960e54594024c991f643f8f963a08d6e3088b2a28588e61df864e13283d20c482360487ff1fc57e else 0xc5870472b28ac98c360c388850552e0c29f1109c5068a97061c49c85297263c1871109ca900d931e1c1892d2970614f8884d8b0e08e98acc2a2a5c5870474d4188a94361c18a3d0604c5c5870474d464c7871604c2a78a96224868c562c381356603454a40560c5853d5152c4490d186c38310aae3268a97161c0293d3931e1c58128a9cc150b831614e1885218293c5830989c50888921a30d802e2c242c141b160c29cc15a0a900d11243462028ac5830da55223151b161c1169338b0e08e9a6141881911870628f48a1388461c11d35119308322b161c11e90a4f161c098c4e2a224868c2e2c381354283624f870153141588921a32020305c38b058545448623161c09a98c982e2c3813982b4c64d112434617161c02ab14911e2c381345a0a9014911e1c18a2d222224868f161c09a2d45450688921a311870628b60a1112195c5870454d5158c9a224868c508c587045b49900d8b0e08e3a84b870628e3a626192e0c5863ce2a2a5c01b0e28e42927152900c2b062c31ea204f160c31c74e1b062c31d2cc182e08f8b0932140a0d8a3e1c04e71443062c31d2cf831618e949cc4c562c38238e9d325c3831471d393c38b0474d30a8a970e2c11d3504e2a50d870628f4138b871608e))
def lay495r10 : Packing := (201,2,5,63,0,14,1,word495r10)
def keys495k11 (i : Nat) : Nat := 0x175854e561a6ad78317c1fc56ed853047400000000068ea71e8bc9c000001b5d81710a001a6ed6200195273d0c3c076cc0004ab189a54ec92fb2e8c7b51b564460334000453ea2000000000f5e001a48e056a8001d10c24e72000000000001a630df126eb38848b58a76360000010ce000069ad20881850b800000052907c98fe4f73e000000001c5fa420012f0421946001af2858536001f6f28ca0f0cab5a0e02b6000000f2de22281a40a26f42eafcea34521098a1488c7af78a5a2d29306705c000001ce20012d012bc3bceda9600021ded6001a5bf76d86cbe432001ae4b18808087b03b130a08e7a3e76b8ba95774b00bd6c0d5523a002ad382e82a0cd69a2ec358146dd10801ae31c03f4d84777e2bc4288c5d66a7fd25a998ffe78d2fc95d3289bd007740efeb070569eb1e17b71cef91702db51590cc4d844afd890ec083d15473b2f5b06d72018b41f8142bf20e77c6558d750000001d90001c1226c000438850a4bb39f7cb0e0c00b0800c9406340862414003000040116483020608001020c80f1c0cf800c0000d24d3f83060c0094a0cc010220c061c284b216003ac1850200
def cut495k10p16 (i : Nat) : Nat := 0x809040000000000021088
def word495r11 (i : Nat) : Nat := 0x1678a18069851958228479c51a78608a62a78a18069861558a18079c614a9e28609c51889e28219d59c68a18059c66488a18079c61489e28609d52a78a18059c65678a18059c51a08a11e61858628079861488a18079c69e28609628601e49e28609059e28609628601e4caafab42a69da46859e66d986559263f0d22887e1804207800ffcefff5dbfebaffc75ffacbff957feba7fc74ffac9ff553fe2a7fe44ffae5ff54bfea15fe77dfccddf957df227ee22
def lay495r11 : Packing := (20,1,5,63,0,10,1,word495r11)
def keys495k12 (i : Nat) : Nat := 0x24400000000001250028e5e00c20000046000000000000019a47470000000000000000005a40000000028560007b000000000001aa098030252e47ac0000000000000002400000161
def word495r12 (i : Nat) : Nat := 0xe20824ff
def lay495r12 : Packing := (1,0,5,63,0,0,1,word495r12)
def samp495 : Array (Bits × Bits) := #[(0x44b33048000dd96006600090f51400cccc0001a9002400fff9ce7003ff,0x44b3304d2204d974967490905516a1cccea200a9a8a6a26a38c63a8aa3),((~~~(0x7f3fc3efffed9e7ff800031d39e7ff0f0ffff931ffc7ff3ff18c6003ff : Bits)),(~~~(0x7f3febef9dff9e7e6d5e631d39e79e0f0f9dfd31e7479d39d5ad6e739d : Bits))),(0x803c260019c7e0007800003082000ffffff98f0003fff000f83e00000,0x8014263079c7e0c378c300008218555558788f061ad87186f83e6298a),(0xfc000001e07ffff80000fc0fc000ff0000e0ffffc000000ffc000000,0xd4000026a06ba0b800b0b40fc025ff0026a0fb09c026026ffc00a82a),(0x0,0x0),(0xf00038001ff8000000007000fffff000000ff00000000000fffffffff,0x900038215fb00086008610008610e00010cfd0045011411452944711c),((~~~(0xffffc0001fffffffffff8000fffffffffff0000000000000fffffffff : Bits)),(~~~(0x6fffff6fa7fffffebffeb8b45fffb7ffffb7a8fbe9efa77a7ffffebfaf : Bits))),((~~~(0x3fffffffffffffff800000000000000ffffffffffffffffffffff : Bits)),(~~~(0x90143fb9fffffee7fee790008618f55558fffff67fd9fd9fffff67d9f : Bits))),((~~~(0x7ffffffffffffffffffffffffffffffffffff : Bits)),0x6f2beb6f815f945e055e00000003800003800000e003803800000e0380)]
def cols495 : IndexTree ColumnInfo := (.fork 13 (.fork 6 (.fork 3 (.leaf [(1,0,494,0,11),(2,0,493,0,11),(8,0,487,0,11)]) (.leaf [(4,0,491,0,10),(128,0,367,0,10),(32,0,463,0,9)])) (.fork 3 (.leaf [(256,0,239,0,9),(132,0,363,0,9),(0,32,332,131,8)]) (.leaf [(0,128,331,36,8),(64,0,431,0,8),(258,0,237,0,8),(264,0,231,0,8)]))) (.fork 6 (.fork 3 (.leaf [(0,2,205,288,7),(0,4,299,192,7),(0,8,167,320,7)]) (.leaf [(0,256,165,74,7),(1,32,332,130,7),(2,32,332,129,7)])) (.fork 3 (.leaf [(4,32,328,131,7),(4,128,331,32,7),(32,128,331,4,7)]) (.leaf [(65,0,430,0,7),(72,0,423,0,7),(128,32,332,3,7),(160,0,335,0,7)]))))
def lv495 : Nat → Packing
  | 7 => lay495r7
  | 8 => lay495r8
  | 9 => lay495r9
  | 10 => lay495r10
  | 11 => lay495r11
  | 12 => lay495r12
  | _ => emptyPacking
def ix495 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 2 10 0 7 3 0 keys495k8
  | 9 => lookupWord 100 343 7 13 9 0 keys495k9
  | 10 => lookupWord 210 734 7 14 10 0 keys495k10
  | 11 => lookupWord 67 242 7 12 8 0 keys495k11
  | 12 => lookupWord 6 69 2 9 5 0 keys495k12
  | _ => fun _ => none
def g495 : Forest := ⟨495,12,fun j => samp495[j]?.getD (0,0),cols495,#[[]],lv495,ix495,noFactory,noFactorySound 495⟩
def word503r7 (i : Nat) : Nat := 0x583cb85d9655d154
def lay503r7 : Packing := (1,5,5,63,0,0,1,word503r7)
def keys503k8 (i : Nat) : Nat := 0x8d80
def cut503k7p0 (i : Nat) : Nat := 0x80884
def word503r8 (i : Nat) : Nat := 0x78fc5e1f0480000000700100000000060039ecc64b1986c05eae96eb458ab956a852a893e9c4ca59269046a290e84409f8f6783a9c8de6c34998c6602e968ae54289389648228c05a2a1389042198b44e210d8541e008ffaa8985d564adf69e99614648ffaa9981d464cfe681981d464afeaa97560064cfe29990a2154cfe65990a2154afe6828821954cfda219121954cfd61d9121954cfd21d9121954ddd69591219548ffaa8985d954afe682885d954bed684865d154f1f5d9655d1549f768e995d8548ffaa9981d854af7aa97660c54cf72a57660c54eb76597660c54cbf2a1961d6449fb68a9959644c5f65c9761464d8f65495590649af6a47559064aaf6a07559064e5e5d475600649cf2a5655d154dce6829955054bce6829955054d8f6589655054acf6a07655054e375d87660c54b4faa9751d644f0f999751d644b8faa96519644f0f5d87695644add6849761464ade6809761464ccf615941d4648fe6a47560064abe6987560064aee6907560064af668c7560064afc68475600648fe6829961954f0f5d9655d154af66807660c549edaa99121644dad99991216449afaa9961d644dae999901d6449eb68a99596449edaa99119644bce6809895644bce6809695644bce6807695644f0f9de66956448fe68098956449ee6829955244
def lay503r8 : Packing := (61,4,5,63,0,9,1,word503r8)
def keys503k9 (i : Nat) : Nat := 0x3404e1980b9879424820f0e80246a5007bab364d02b8ed2153ce6431a3084a25b400043475ca0a000000093b988ba9c0000002c4e05200000058dc0000000002019c6a2160004837758831e12f43dc1ee63e1b4327290a88a315845c1980ef2050f00018330007a824200007e40000001f66400851bc374e680261db814000f1d2a4dc646c6000000000019c1620c53a41c2b81188e700a947717f0bbc7721ffe942456ab3b94343b1c40781c100689384fa3860a602f435c13910b0218ea48318544c14b0465481c830088534a00b0400050892d225d080
def cut503k8p23 (i : Nat) : Nat := 0x8090400000000000408840000000000040884000000000004088400000000000809040000000000021088000000000002108800000000000210880000000000040884000000000002108800000000000822100000000000080904000000000008090400000000000409040000000000082210
def cut503k8p38 (i : Nat) : Nat := 0x1110402202108502109108001121041e111040220210850211104022021084e210910800112105d211104002021084de11104002021084de11104002021084e211104022021084c211106022021084c211104022021084c220a100c404191186111040220210850211104002021084e222241000428210522244240601a281e211104022021084c2111040220210850211104022021084c211104022021084c211104022021084c2111040220210850220a1000404091122
def word503r9 (i : Nat) : Nat := (if i < 1 then 0x90fe3e244e1e00d1c1c170f0b070312707c6c3c2c1c00544201f1b0f07002b10707c6c3c2c109c41c438f8b851380347c0071c1b0f0b004b107000100fe3e2e1e0440da300104040c0848700803a0048b00803a0070098204a0080000021a138f8b87826200e0d0bc5c4e3e2e1a616138b8782525e3e2e0909c978f8b8782627e3e1e02a949f8f8b84a652625e3e2e0978f8b87824e02dfcdf6df0deade4ddedd8dd2dccdc6dc0dbadb4daeda8da2d9cd96d90d8ad84d7ed78d72d6cd66d60d5ad54d4ed48d42d3cd36d30d2ad24d1ed18d12d0cd06d00cc2cbcc76c30bf2bb4b66b28ae2aaca6ea40a0a9cc99e96892291c8e68b887285c8568207ea7a47667286f26b46766386226146065f85ea5dc5ce5c85ba5a459658856a54c53e5305225145064f84f24a44664283e23a436632831a2dc2d62d028a27c26e26825a23c22e2102021ec1d61d01ca1c41be18813a10c0e60b0082054026000dfecad10b25ff656885937fd1042ac97fd9721564dfec390ab26ff21c855937f930baac9bfe885d564dfe4bb0a325ffa65751937fb2d442a97fd96a2154dfe4bb0caa6ffa2086552ffb2e432a9bfd8721954dfe4390caa6ff261765537fd10bb2a9fbc865d154fbeb2ae8aa7df595645537f92ec30a97fe995d854bff4caeb226ff26175912ffb2c3ac897fe9959644dfe4c2cb225ff65d65913dfaecb2c897fd9719644f5f4cac8327af65564193d792ab20c9ebd7559064f5e3aac8327cfa6554153e7b2caa0a9f3c9655054f9ebb2a82a7cf1d954153afaea3ac89e7d65196449fecad10b26df614855927f930baac9b7e9961464dbecbb0a326df25d851927fd32c28c93fd985d464dbec2aea324ff66075192f7b283a8c9bf97560064dfc3ab00324ff65a885537f321442a97f990a21549ff4cb0caa6bf61886552feb22432a93fd985d9549fe4c2ecaa6efa2174553e792aba2a9f3d655d1549fecc2c8aa4ffa65861527fb30bb0a9afd865d8549fecc0ec2a6f7659831537baecc18a9bdc7660c54bdeca90d227af26266912f7b2e42c897bd9621644f5f3310b225efa6575912f7930bac89ebe665d644bdecb0eb227af99875912f7d32b2c897bc9859644bdecbacb227af5d965913e790ab2c897bd9719644f9e4c4ab227cf25a55913e790d2ac89f3d7695644f9e3b4ab224ff262669127f930bac896fd961d644bdeca0eb225fb64875912ff3203ac893fc9859644bdeca0cb225fd64465913afcef2ac89e7e66956449fe4c4ab225efa6564913d7cccb2489f3e5559244bdf4caa9225ef65d54913b7ceeaa4897bd9655244f5f332a9227cf59554913e7caaaa4896be9959064b9f4caa82a74f5d475913c7aca32c8937e99614649fcc8510aa4f7a6583152f6b2242c896bd961d644bd6c90eb225ee64075912f6b2232c89e3e6695644 else 0x703020100050e1e007060504e3e2e1e0a19c1896138f8b8782806046361e2e00e9e1a138f8b87819e710070605e3e2e1e0842418100c078b803a70706a3a104e2e00e238f8b8780951262725e3e2e1e0449e1b8f8b8622586e3e2e18865981c0c080400983c7c4e3e2e10d978f8b858038366100f0ee3e2e1e00da203326e361e2e0980c08040034507060504e3e2e1e0a2158020014138f8b8782607030102e00d18401e178f8b87821080504010003e20f1c1d17838b878d10745e3e2e1e044999c15898580443270c11e08584e2e19c3216138b87819a722e009101e0078018487021e0060c0049a122c0878012322c00c9f00943e007001448496144058e18040381c178f8b87811)
def lay503r9 : Packing := (132,3,5,63,0,12,1,word503r9)
def keys503k10 (i : Nat) : Nat := 0x5b60fc000284920b82135427eb260000e5bd436881f1008c0faeb2e833426564500000a18746fc0a371c297a60834c7828c385680e08028422fb69349fa40358c5303d428c0c6823c836003aa204937fb2fe225013340d681ca05474cc10e814be0dfc1b8c348000000180241a5e8060001a83f40ae1740001a000138000062dc0000c0be83ab0aba0f40000000861d21e38173a81e24b01800100000fade00000000000f0d000002a6802614fea0e683618593071c5f6111e07aa49914a8000686ad0c880d5889804afa9781accaff00d600a205948cd0343078000382b8000d4065d2f220581080e86153c406883f025219700ca17670e240ad919922400002d344bc0000544b6160ca68000b01d81f800060030001c03044100000001d96cca16018c2788d9a9b5d83b00000000a87c014a6648139941a90280f8b9b2108b672c0ec91bc431a867c0e7a1fe88fe82c60970528000185d000061d7c29884682c00909414d51612f96d91c10e64b90488caf824086674af4c06d94621e1628604f4218879b0c4310782d990ece666c6768d5501d23ac17c0000000a6349442b2d1a002a98e08d403d28260c3746c000092630a420c0000224046df712c0000000604f092ec0f7d689420290702d40442005617bc04636800000003c0080250080000140d8000505f25e4000632d706e21c9008902230ee84e89012f4c0001b047b38907db0f70c818288000201785ac09f9050860994b5c2168320000603c1462a0880b020011d0014380060800624341843218280080092c02843052400608006c0111e001842000101000012c040818e12280030218001080010022040250424a0a02541a7
def cut503k9p9 (i : Nat) : Nat := 0x40884000000000002108800000000000809040000000000040904
def cut503k9p88 (i : Nat) : Nat := 0x4088400000000000408840000000000040884000000000004088400000000000408840000000000021088000000000002108800000000000210880000000000021088000000000002108800000000000809040000000000040904
def cut503k9p100 (i : Nat) : Nat := 0x11104022021085021110502206108502111040220210850211105022061085021110502206108502111040220210850211104022021085021110402202108502111040220210850210910800112104161110402202108502424402080822418e11105022021085021110402202108502222410004282109a111060220210850211104022021085021110402202108502111040220210850222241000428210962244240601a5025a812402100414418e1110402202108502111040220210850220a100840409114a1110402202108502111040220210850220a100840409114a1110402202108502111040220210850211104022021085021110402202108502
def word503r10 (i : Nat) : Nat := 0x18263c58700d9d3a5c78b0e01b386098f161c0967203c3860a1070dc78b0e0b080e8d8f161c11284f1b1e2c3812c4a0705098f161c03681c9d363c58700da0284c78b0e04d3901c1c305083c6e2c38f05919307c7882e1c0106d51d386098f105c3806d4407c5c18b0e3894278b8f161c09a2511d3c54b8f161c09a2541e3260b8f161c11290f1b1e2c382225a23a70c170e3c18a2531c363c5870444b4474f19363c587025895070a3c6c6898f161c15074a38304c78b0e0a43861c362c4c78b0e0a870d0e9a2c41f8f0e2c15854e1e28dc78b0e0a43a61f8c284c587052131e2c38134c131e2c3812cc9d325098f161c1427098f161c09674e99284c38f062a0226c78b0e04b3c74d171e2c3822511e325c78b0e0894274a18263c5870509d305098f161c1400006098f161c1306c78b08894885098b0e099344c78b0e0992c4c78b0e09a7d26f661a4b23ba2c21ca0d1ff5e8dd5dc2db35a3d90d7f97015ed4f53c5295181050f04df0cdcc1cb5ca649888907b46bc5c44cc3d43bc3a42e42401800c0003ffa2164ffd85593ff21564ffd75593ff5d464ffc75193ffa2154ffd86553ff21954ffd76553ff5d154ffd64553ff5d854ffc76153ff99a44ffd75913ff1d644ffd65913ff19644ffe55912ffa2164bfd85192ffa2154bfd86553ef5d154bfd86153ef21a44fbc85913ef5d644fbc75913ef59644fbc65913bf99a44f7e55913ef59244fbd54913af59064f3d54152df61464bf980192f760c54ebe66913cf95644
def lay503r10 : Packing := (43,2,5,63,0,12,1,word503r10)
def keys503k11 (i : Nat) : Nat := 0x5148000041e4e000782c7874dbb061a6693041d8426189422409f0758790bfa97000000312a20fba6720d552822d334aa24046263155a1c5960510005d6199c00000d4891803663603e92504379e501c88e51225a3239871031b5fe6ca85ac2044d0006a7d917adae007814000019964fa330250280002b60000000a29889dd260000128857cb71483a1800301b4ccfa5206d2b2a80709901042f60aa033850e9701f1294b3691e408130077c0400d821811852802c22c00c104b448001400012001433
def cut503k10p5 (i : Nat) : Nat := 0x408840000000000021088
def word503r11 (i : Nat) : Nat := 0x1c51848e2860a068e28601261c61448e2860a058e28601261c61638a1804a048e28609792ea11689003feb27fc64ffaa9ff153ff227be44
def lay503r11 : Packing := (6,1,5,63,0,8,1,word503r11)
def keys503k12 (i : Nat) : Nat := 0x3440000050c0000009003d8003920000000199000e8000000000000042630000000000000d4c0000085d8c0000000000000000000000003c05c9a98340000141000003200000000000000cc000000000000000000000000000e88000000100
def word503r12 (i : Nat) : Nat := 0x620824ff
def lay503r12 : Packing := (1,0,5,63,0,0,1,word503r12)
def samp503 : Array (Bits × Bits) := #[(0x112cc0240003765800cc00001e2800acc00660002193e4007ffe739c007ff,0x112cc0269081365d22ce91000a2d41acea167508009166a1350e318ea1543),((~~~(0x1fff0f77fffb679fff000059a7cfff30fff87fff391cc7ff9ffc6318007ff : Bits)),(~~~(0x1fffaf77cb7fe79f95abca59a7cf3630f9a87cd7bd1cc7969cb56b5b9672d : Bits))),(0x20f043000671f8000f00000614000f00007ffff18fc3fff8003e0f800000,0x205043181e71f8306f18300014305f01832ac1d08b42d838c1be0f98530a),(0x0,0x0),(0x3008c000781fffff000047818000fffff80003e0ffc0000003ff0000000,0x8c00da81ae81f000f4281801df540f8007be0ffc01b00dbff001d03a),(0x3c00f00007fe0000000007801ffff0000000003ff0000000003fffffffff,0x2400f01097ec00214010a4801c2160010a00853bd00011208914a511622c),((~~~(0x3fff000007fffffffffff8001fffffffffffffc000000000003fffffffff : Bits)),(~~~(0x1bfff637d1ffffffa7ffd3800bff67fffb3ffd9d08b56fa3bd1fffffa7f4f : Bits))),((~~~(0xfffffffffffffffff800000000000000003fffffffffffffffffffff : Bits)),(~~~(0x2450ffdcffffffb9ffdcfca81c31ff558faac7ffffffd9fecfffffd9fb3f : Bits))),((~~~(0x7ffffffffffffffffffffffffffffffffffffff : Bits)),0x1bffa637c057e51780abc0000007000038001c00000003801c00000380700)]
def cols503 : IndexTree ColumnInfo := (.fork 10 (.fork 5 (.fork 2 (.leaf [(1,0,502,0,11),(2,0,501,0,11)]) (.leaf [(4,0,499,0,11),(16,0,487,0,11),(32,0,471,0,9)])) (.fork 2 (.leaf [(64,0,439,0,9),(128,0,375,0,9)]) (.leaf [(256,0,247,0,9),(33,0,470,0,8),(65,0,438,0,8)]))) (.fork 5 (.fork 2 (.leaf [(68,0,435,0,8),(0,1,406,96,7)]) (.leaf [(0,16,103,384,7),(0,32,340,131,7),(0,64,178,261,7)])) (.fork 2 (.leaf [(0,128,323,52,7),(0,256,165,82,7)]) (.leaf [(48,0,455,0,7),(66,0,437,0,7),(130,0,373,0,7)]))))
def lv503 : Nat → Packing
  | 7 => lay503r7
  | 8 => lay503r8
  | 9 => lay503r9
  | 10 => lay503r10
  | 11 => lay503r11
  | 12 => lay503r12
  | _ => emptyPacking
def ix503 : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 3 0 6 0 2 keys503k8
  | 9 => lookupWord 32 118 6 13 6 3 keys503k9
  | 10 => lookupWord 82 290 7 15 8 3 keys503k10
  | 11 => lookupWord 31 108 6 13 6 3 keys503k11
  | 12 => lookupWord 6 74 3 10 3 3 keys503k12
  | _ => fun _ => none
def g503 : Forest := ⟨503,12,fun j => samp503[j]?.getD (0,0),cols503,#[[],[33,101,135],[16,66,134],[16,64,32,133,101,118],[32,16,65,101,117,133],[32,65,117],[64,133,118],[64,33,117,134]],lv503,ix503,noFactory,noFactorySound 503⟩
def word511r8 (i : Nat) : Nat := (if i < 1 then 0x46917451114390b42105408ff3f0f93d8f33c0ed3a8e7390e1378db360d5348cf330c9318c3300bd2e8b72d0b12b8ab2a0a52889f27099258932408d22887210811f87b1e0751c86f1b069198631805d16857150511384b120451083f0f0390d8330c02d0a827090210781b060150480f030090180300107ddda32e88999931d68f5ba85b96cd1130b2e1f32ddc32d9a226165c3f45bb805b3444c2cb53e9d0a65b2261865970bdbae653644c2ecb2e1db754ca6c8985d965c3d6ea194d9130bb2cb87cdd3329b2261765970fcba2653644c2ecb2e1fa740ca6c8985d965a3daea170dbb424b4ab47d5d32e1b7684969568fcba45c36ed092d2ac1fe770a96c08799a55853eedd98d294ac310d705dd3329976199521ae0f3a06532ec332a43681fb32aa65d8665486b82ee998acbb0cca90d706dd2315976199521ae0f3a062b2ec332a4348b7b74cbaa98664c86b926e916ec332ac990d7259d02dd866559321ae473a85bb0ccab20435c9674cb76199564086b934e916ec332ac810d7271d12dd866559021b05bbb664d10d190d3360b7b31a86cca865875e12ed436ad9950cb0ebc275a86d5b12a1961d785ab50d9b625432c3af09e6a1b56c0a865875e15cd4368d8150cb0ebc2d9a86cdb02a1961d785e350d8b605432c3ae8ae711c06a58621875d16ce1b80d4b0c430eba2f1c1701a9618861d740fb92d3b0cd290c3ae0b7aedc9619a321875b12eecb0cd2b46430eb6279d9619a5680861d6c573b2c3348d010c3ad8b67658668da021875b178ecb0cd0b40430eb0c7cdcaeda6299751d72a7388e0372432ea3ae55a709c06e4865d475916e6e350d330cc98eb42dedd6e986219931d784bb74c336a433263af4176dd866d48664c75e16cdd30cd810cc98ebd259866d5b0219931d7a5330cda360433263af4b4619b16c08664c75e13cdd30cda90cc80ebd079b7619b5219901d7857374c3368433203af42e6dd866d08664075c96d6630cd990cc80ebc2d9ba619b3219901d7a1b36ec3366433203af496619b56cc8664075e94cc3368d990cc80ebd0e9b7619b2219901d7a5530cda364433203af4b2619b36c88664075e178dd30cd890cc80ebd271866d5b1219901d7a5a30cd9b62433203af4b8619b26c48664075a876eb98cd9130c32cb52add4319b226186596a59ba6633644c30cb2d4b9744c66c89861965b16ce8532c3346432cb8a79b8700a82957659718f36ee014e5330ab2e81f2a5c825d7661565983eee1304baecc2acbc07cbaa65875d98559614f9b95db50542ca32d49e740b86617659465e42f5dceec3346434ab685edd69d8668c86957c0bb533bb0cd190d2ada1bb75a7619a221a55f41d3bb0cd2340434abe85a77619a368086957d0e4eec3342d010d2ad29736a886cc8699a55 else 0x0)
def lay511r8 : Packing := (95,6,5,63,0,10,1,word511r8)
def keys511k9 (i : Nat) : Nat := 0x120f0005902495a42105412ec8700cd16c0c5c4c400e1e584c46e43ab12e04646800041cc80d84125ba2c8913046c27211193680e00090ac860051a35c24d850ca7848b1fd8d8043430d080000001e2c11e8000000a4522f495351b602720e0beca3a3ea23495445404ea87789203b806815e80483c41c914b148c240007029958001c5702e782c000658a0d306d02f24fc048003809e5d00068ccc100004239f418b481662660b987000070ca0ed064000e0f8e82028036990240c0008ce00c09e6301a38ce1
def cut511k8p0 (i : Nat) : Nat := 0x80904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000408840000000000040884000000000004088400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080104000000000002108800000000000210880000000000040904000000000008088400000000000210880000000000080884000000000002108800000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904
def cut511k8p64 (i : Nat) : Nat := 0x80884000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904
def cut511k8p80 (i : Nat) : Nat := 0x109108001121041611104022021084c211104022021084c211104022021084de11104002021084e21110402202108502111040220210860211104022021084c211104022021084c211104022021084c211104022021084e211104022020084c211104022020084c211104022020084c21110400202108522
def word511r9 (i : Nat) : Nat := (if i < 6 then (if i < 3 then (if i < 1 then 0xf07e9961d766156587ddc3aeda666065b1f5c12de8865c65a3f9c02a1985d865c779b96c2aa59465b36dc22a19859465a37dc9aaa8859465b3b5c12de886506597b9c02e1a76506587bdcaaed876506587bccbaa98765065c7baaa6c08765065979dc3aed866506597adc2aed766506597b9c02e17665065e2beaaa226665065b6b9c021e66650658f6dc2aeda625e55ad75c12ea7725a55ad75c72e1a125a55af35c42e1a125a55af55c32e1a125a55af65c22e1a125a55af71c02e1a125a55cd76bb9dda125a55ad5dc3aaa7761a558d7ecc6dca921a55c57ebb6a5a721a55c57dba6a67721a55ad5dc32a67721a55ad6dc22a67721a55ad79c02a67721a558e7dcaaed8621a55cd5ebb9dda321a55ae5ecc619a321a55ec5e77619a321a55ad5ecc69da321a55e55da99dda321a55ab6ecc619a221a55ad6ecc69da221a55cd7abb9dda021a55ab7acc619a021a55e97a77619a021a55ad7acc69da021a55ad79ca9dda021a55e579a99dda021a55ed3a77691a021a55ed5a7768da021a55ed6a77689a021a55ed7277685a021a558f5dc3aeda85da558f6dc2aeda85da558f7acc6c0a85da558d7ecc2e9875da55ab79c02a1865da55cb79a86c0981da558d7dcaaed761da55af71c0261a11da559e79c02e5a899a559e79c02e89899a559e7acc6c09899a55b27cc96ea8899a55b87cc76ea8899a55ba5dc32ea8899a55ba79c02a68899a559e7acc6c0a799a55da7a886c0a799a559e3dc4aed8799a559e7acc6c08799a55bc79c02a67799a55bc79c02627799a558f5dc32ea8899a55da76886c49699a55dc76776c49699a559e5dc3aed8699a559c7ecc6dc8699a55d87e886dc8699a559e3ecc6d08699a55da5e886cc8699a55dc5e776cc8699a55da6e886c88699a559e76cc6c48699a55dc76776c48699a55da7a886c08699a55dc7a776c08699a559e79c02e17699a559e76cc6c47699a55da76886c47699a55a5f5c72e1a125a55a7b5c42e1a125a55a7d5c32e1a125a55a7e5c22e1a125a55a7f1c02e1a125a55c5f6bb9dda125a55c3f9a86c0981da55a7f1c0261a11da5596f9c02e5a899a5596facc6c09899a55b2f9c02a68899a55b4f9c02a67799a55b4f9c02627799a55a3f9c02a68899a55a5f9c02a67799a558f6ecc6c8a859655ab79c0aaa8859655ad79c0aaa7759655ad6dc22a27759655ab6dc22a18659655ae6dc22a26659655e07eaa65d8665486d25ebb6199564c86d27abb6199564086a2dcc9a21a321a66c2dda86cca865875a2ddc9619a321875c2ddba6188664c75d2d9866cc8664075b07cc961d7661565ca5ebb619a321a55e85e77619a321a55e25da9619a321a55e85da7619a321a55e86da7619a221a55ea2d86691a221a55ea4d8668da221a55ea3986691a021a55ea598668da021a55ea7186685a021a55 else (if i < 2 then 0xe6e996689a021875e6f196685a021875b2ddc32d99899875b2f5c12d99899875b2f9c02d99899875d27d986d48699875d2dd986cc8699875d2f5986c48699875d2f9986c08699875975dc52e1a664c7597d5c12e1a664c7597d9c02e1a664c7587dccb6a1a664c7587ddcaaed8664c7587dccbaa98664c75e2dda86998664c7587decc6e88664c75c6ddba6188664c75975ecc6d48664c75c75eaa6d48664c75c75dba6d48664c75d55db76d48664c7597dacc6c08664c75c7daaa6c08664c75d3d9866c08664c75c7d9ba6c08664c75d5d9b76c08664c75d759b56c08664c75d799b46c08664c75d7c9b26c08664c75d7d1b16c08664c75e2deaaa226664c75a6ddca21a6664c75b65dc521a6664c75b6d5c121a6664c75b6d9c021a6664c7597d9c3aed866407587facc6e88664075c3f9baa20866407595facc6dc8664075d1fa886dc8664075c5f9ba6dc8664075c3f9ba6188664075977acc6d48664075d37a886d48664075c779ba6d48664075d579b76d4866407597bacc6d08664075d3ba886d08664075d6b9866d08664075c7b9ba6d08664075d5b9b76d08664075d739b56d0866407597dacc6cc8664075d3da886cc8664075d3d9866cc8664075d6d9866cc8664075c7d9ba6cc8664075d5d9b76cc8664075d759b56cc8664075d799b46cc866407597eacc6c88664075d3ea886c88664075d3e9866c88664075c7e9ba6c88664075d5e9b76c88664075d769b56c88664075d7a9b46c88664075d7c9b36c8866407597f2cc6c48664075d3f2886c48664075d6f1866c48664075c7f1ba6c48664075d5f1b76c48664075d771b56c48664075d7b1b46c48664075d7d1b36c48664075d7e1b26c48664075a6f9ca21a6664075b4f9c721a6664075b679c521a6664075b6b9c421a6664075b6d9c321a6664075b6e9c221a6664075b6f1c121a6664075a6edc62dda226165a76dc52dda226165a7adc42dda226165a7cdc32dda226165a7e5c12dda226165a7e9c02dda226165a5edc72d9a226165a76dc52d9a226165a7adc42d9a226165a7cdc32d9a226165a7e5c12d9a226165a7e9c02d9a22616583fccbaa99826165a7e9c0a65a226165a3f9c0aaa8865d65c3eda86c89825d65a7f1c0a65a125d65a5f5c7261a125d65a7e5c2261a125d6593eecc6c89861965c3eeaa6c89861965a5f5c12e5a721965a5f9c0a65a721965a7b9c0a65a421965a7d9c0a65a321965a7e9c0a65a221965a7f1c0a65a12196587f9cba65a02196587ecca6c8985d96596ddc3aed989996596f5c1aed989996596f9c0aed989996596eecc6c8989996596f9c0aed9799965b2edc22618699965a75dc32dca961565a76dc22dca961565a779c02dca961565c37ca96e09761565c774a96c49761565b87dc72617661565b87dc825d7661565f07cc961d7661565 else 0xaa7ccaa208699a55d87cb861d7699a55c3f5b82e1a125a55c5f5b72dda125a55e87da7619a521a55cadebb619a321a55e8de77619a321a55ea5d866d5a321a55e8dda7619a321a55ea5d86695a321a55e8eda7619a221a55eaad86691a221a55eacd8668da221a55ea7986695a021a55eab986691a021a55ead98668da021a55eaf186685a021a55da5d866cc865d655da5d866cc8659655da79866c08659655ac7cca61d7659655a7cdc22d5a3a6586d2ddb86d9a3a6586a7cdc2295a3a6586caddb86d9a3a6586877dcaaed9525586c6ddc36e6aa61886c6ddb96ceaa61886975ecc6cca765486c75eaa6cca765486c76eaa6c8a765486977acc6c0a765486c77aaa6c0a765486975dc3aed8665486b55dc32e99765486b579c02e99765486c57ebbaa99765486b55dc32d59765486b56dc22d59765486b579c02d59765486c6ddcaaed8664c86a6ddcaaed8664c8687ddcaaed8664c86b74dc22dd9564c86b759c02dd9564c86d3d9c3aed8664086b3d9c3aed866408697d9c3aed8664086b5b9c42d59764086b5d9c32d59764086b5e9c22d59764086b5f1c12d59764086b739c42dd9564086b759c32dd9564086b769c22dd9564086b771c12dd95640868ef5c1aeda5262669adecc6cca9a2266caeebba21a225666ae6dc525da225666aee9c025da2256668eddc32e5a6a2266aaddc3aaa8861a66ae3dc42dda521a66ae5dc32dda521a66ae6dc22dda521a66ae75c12dda521a66ae79c02dda521a66a76dc525da225666a7e9c025da22566686fccbaa9962597587ddc32e6aa6197596ddc3aeda86587596decc6cca865875c6deaa6cca865875c6dda86cca865875d2dda86cca865875d65db56cca86587596f6cc6c4a865875c6f6aa6c4a865875c6f5a86c4a865875d4f5b76c4a865875d675b56c4a865875d6b5b46c4a865875d6d5b36c4a86587596facc6c0a865875c6faaa6c0a865875d2f9a86c0a865875d4f9b76c0a865875d679b56c0a865875d6b9b46c0a865875d6d9b36c0a865875d6e9b26c0a865875d6f1b16c0a865875c3dda86cca865875c3f9a86c0a86587587ddc3aeda961875a6ddc3aa99661875b2ddc32e19661875b2f9c02e19661875c7b9b46c1a921875c7d9b36c1a921875c7e9b26c1a921875c7f1b16c1a921875a67ecc659a521875c67ebb659a521875e47da7659a521875a6decc659a321875c6debb659a321875e2ddc8659a321875a6ddc9619a321875e2dd98619a321875e65d96695a321875a3facc661a021875c3fabb661a021875a6facc659a021875c6fabb659a021875e2f9c8659a021875a3f9c9619a021875e2f996619a021875e1f99869da021875e4f9a7659a021875e37998695a021875e67996695a021875e6b996691a021875e3d99868da021875e6d99668da021875e3e998689a021875)) else (if i < 4 then 0xcd5dba6cc865d475d55db96cc865d4759d7acc6c0865d475cd7aaa6c0865d475d979866c0865d475cd79ba6c0865d475d579b96c0865d475dd39b46c0865d475dd59b36c0865d475dd69b26c0865d475dd71b16c0865d475cc7dba2ea665d475e87da82a2665d475e87eaaa22665d475ac7dca21a665d475b47dc921a665d475bc5dc321a665d475bc75c121a665d475bc79c021a665d475a6dcc66a1a664c75b2dcc86998664c75b2decc6188664c75d2debb6188664c75e2dcca6188664c75d2ddba6188664c75e2ddba6188664c75e2deaa6188664c75f25d866d48664c75f2d9866c08664c75d2ddb82e26664c75d2f9b62da8864075b2facc6188664075d2fabb6188664075e2f9ba6188664075f0f9b76188664075f279866d48664075f2b9866d08664075f2d9866cc8664075f2e9866c88664075f2f1866c48664075d2f9b82e26664075c3f9b82e1a0a6565c5f9b72dda0a6565c5edb72dda226165c6edb62d9a226165ae6cc66d5a226165d2ecc66c898619658afdcaaed8621965b2f9c0a658621965aadecc619a321965e2de99619a321965e2dd97619a321965ea5cc5619a321965e2dd98619a321965aafacc619a021965e2fa99619a021965ea78c5619a021965a67cca6d6995d965ae6dc2aa8a55d965ca7db82a0a55d965ae79c02a0a55d965b2edc2261865d965aa7dc825ca6615658e7dcb29ca661565cc7db729ca661565ae79c029ca661565d33c986d0a661565d87db76188661565da5d866cc8661565da79866c086615658e7ecc2e97661565c67cbaa657661565e47ca925d7661565f07c9825d7661565b17cc961d7661565e27eaa2626661565b27cc961e6661565b0fcc961d7661565ca7ebb6a0a859465ca7dba2ea8859465ea79c0aaa8859465ba79c0aaa8859465e87e8869ca759465967ecc6e48759465d27db9a208759465d17db961c87594659e5dc3aed8659465a67dc9aa986594659e6dc2aed7659465a67dc9aa976594659e79c02e17659465967ccb6617659465d27cb86617659465f07d9861d7659465d1bdb72de8865065b1bcc869d8765065b1becc61c8765065e1bcca61c8765065d1bdba61c8765065e1beaa61c8765065d1bcb861d7665065f0bd8721e6665065cb75b82e1a125a55cd75b72dda125a55da5dc3aed8621a55ba5dc3aed8621a55d87db72dd8621a55b87ecc69d8621a55d87ebb9dd8621a55e87eaa9dd8621a55f07da99dd8621a55ea5db7619a321a55ea5c97619a321a55ea5da7619a321a55f85e77619a321a55ea6da7619a221a55f87a77619a021a55cc7eaa2d9875da55da5d866cc865da55da6d866c8865da55dc6dc2aed761da55bc6dc2aed761da55d87db82e1761da55ca7dba2ea8899a55e87e8869ca799a55b87ecc61c8799a55e87da82a27799a55ca7da86da8899a55 else (if i < 5 then 0xc7f8c96c0a85da5587fdcbaa8985da55a7edc2aa8985da55c7f9ca6c0985da55c7f8ca6c0985da55c7faaa6c0985da55d5f9c76c0985da55c5fcc92e9875da5596fdcbaa8965da5587fecc6e8981da55c7f9ca6c0981da55a7f5cb261a11da55e3f5b8261a11da55a7f5c6261a11da5587fecc6e0a999a55c7f9c86c0a999a55c7f8c86c0a999a55c7f9c76c0a999a55c7f8c76c0a999a55a7f9c02a4a899a55c7f9ca6c09899a55c7f8ca6c09899a558fddc32ea8899a55a7f9c02a68899a55a7f9c0261a799a55a7f9c02a4a799a55a7f9c02a58799a55a7f9c02a48799a55a7f9c02a67799a55a3fdc82a58699a55a7f9c02a58699a55a7f9c02a57699a55c75db52d5a3a6586b2dcc86d9a3a6586e2dda8699a3a6586aadcc86d9a3a6586aadcc8699a3a6586ca7db52d6aa61886aaddc32d6aa61886aaedc22d6aa6188692fecc2ea99618869addc3aeda5618869af9c0aeda561886aa7ecc694a561886e27dc9aa98665486ba5dc329d8665486ba6dc229d8665486ba79c029d8665486f07cca65d8665486f07eaa65d8665486b0fecc65d8665486e0feaa65d8665486f07dc565d8665486f07cc565d8665486d65db52d58664c86d2debb619a564c86e2dda7619a564c86d55db72dd9564c86f25ebb6199564c86f25db76199564c86f25cb76199564c86d2debb6199564c86d1f9b72dd8664086d379b52d58664086d579b52d59764086d579b72dd9564086f27abb6199564086f279b76199564086f278b76199564086d2fabb6199564086e2dda96cca9a2266c2fdca2e68821a66d2ddc32e68821a66cc7db72dda521a66e87da7619a521975cadebb619a321975e2ddb9619a321975e2de99619a321975e2dda9619a321975ea5d86695a321975ea7986695a021975eab986691a021975ead98668da021975eaf186685a021975c2fdb82e2aa65875a2fecc6a0a865875c2febb6a0a865875e27da86d4a865875e2dda86cca865875e2f5a86c4a865875e2f9a86c0a86587592fdc9aed862187592fecc6e58621875c2feaa6e58621875a2fecc6a58621875e2ddc36a58621875e2f9c06a58621875b27dc9619a521875e27da9619a521875e87da7619a521875cadebb619a321875e2ddb9619a321875b2ddc9619a321875e2dda9619a321875ea5d86695a321875b2f9c9619a021875e2f9a9619a021875ea7986695a021875eab986691a021875ead98668da021875eaf186685a021875c2fdb96a0a899875c2fdba2e99899875c2fcba6a19899875cc7ebb698a65d4759d5dc3aed865d4758d7ccaaec865d4759d5dc32e8865d4759d79c02e8865d4758d7dcbaa8865d475957ecc6e4865d475d55dc36e4865d475d579c06e4865d475c57dba6e4865d475d47db9618865d4759d5ecc6cc865d475cd5eaa6cc865d475dc5d866cc865d475 else 0xc7faaa6c2995d965d5f9c76c2995d965d5f9b76c2995d96597ddc3aed985d96597f5c1aed985d96597f9c0aed985d965a7edc2aa9985d965a7edc2aa8985d965c7edca6c8985d96597ecca6c8985d965c7ecca6c8985d965c7eeaa6c8985d965d5edc76c8985d965d6edc66c8985d9659eddc3aed865d965af6dc2aa8a55d96597ddc3aed989996597f5c1aed989996597f9c0aed98999658fddc32ea889996597f9c0aed979996587fdc82e99799965c77ca96e09761565db75c86c49761565de75c66c497615659f5dc3aed8661565be6dc2aed7661565e67cb92a57661565be79c02e17661565bc7dc72617661565be6dc22617661565f87cc961d7661565f87cb961d76615659f6dc2aed7661565f87d872997661565be3dc42997661565bc7dc72197661565be3dc42197661565be5dc32197661565be6dc22197661565be75c12197661565be79c02197661565f87d875da6661565c7ecca6c8985d56587fccb6a6885d565c7faaa6c0a766065c7f9a66c0a766065c7ddc3aeda666065a7ddc3aeda666065c7bdc46e6aa61c65c7bdc96d2aa61c65a7bdc4aa99861c6587fccb6a68861c65c7ddc96ceaa61865a7ddc3aa99861865a7ddc3aa99761865c7edc96caaa5d8658fbdc4aeda85d8658fddc3aeda85d8658fedc2aeda85d865c7f9c96c0a85d86587fecc2e9985d86587fdcbaa9985d865a7edc2aa9985d86597bdc7aeda86506597becc6d9a86506597bdc8aeda76506597becc6d9a76506597bdcaaed8765065c7bdcaaed876506597bdc6aed876506597becc6e98765065c7bebb2e98765065b5bdc669d8765065c7bcba6d9876506597becc6e8876506597becc6d88765065d7b9ca6c08765065d7b9c66c0876506597bdcaaed866506597bdc7aed8665065d79dc3aed8665065b7b9c021d866506597bdcaaed766506597bdc8aed7665065d7adc2aed766506597becc6e1766506597bdca2e1766506597bdcb6a17665065e5bcca61d7665065f1bda861d766506587fecc6d8a99de55a7f5c8aeda125a55a7f4c8aeda125a55a7f5c7aeda125a55a7f6cc6e1a125a55a7f6cc2e1a125a55a7f5c72e1a125a55e5f5c72e1a125a55e775c52e1a125a55e7b5c42e1a125a55e7d5c32e1a125a55e7e5c22e1a125a55e7f1c02e1a125a55a7f6cc6dda125a55a7f4c86dda125a55c7f4b86dda125a55a7f5c82dda125a55a7f4cb9dda125a55a7f4c89dda125a55a7ddc32e6aa61a55a7f9c02e6aa61a55c7dcc96ceaa61a55c7dcb96ceaa61a5597ddc32e6aa61a5597f9c02e6aa61a55a7ddc3aa8a961a5587fdca2e67761a5587fdca2e67721a55e57cc969da521a55e5dcc969da321a55e5ecc969da221a55e5f8c969da021a55c7ecc96caaa5da5587fecc6e0a95da55a7edc2aa8a95da558fddc3aeda85da558fedc2aeda85da55))) else (if i < 9 then (if i < 7 then 0xd7f1866c4866407597f9c62e26664075a7facc6e1a0a6565a7facc2e1a0a6565e3f9b82e1a0a6565a7f9c72e1a0a6565a7f9c62e1a0a6565a7facc6dda0a6565a7f8c86dda0a6565c7f9b86dda0a6565a7f9c82dda0a6565e5f9b72dda0a6565a7f9c62dda0a6565e3f8b86a1a0a6565a7f8c869da0a6565e5f8b769da0a6565c7ddc76ceaa66165c7dcc76ceaa66165c7ddc66ceaa66165c7f9c86c2aa66165c7f9c76c2aa66165c7f8c76c2aa66165c7f9c66c2aa66165a7edc7aeda226165a7eecc6dda226165a7edc62dda226165a7eecc6d9a226165a7edc72d9a226165c7ecb72d9a226165c7edb76d5a226165d3f8c86c29926165a7f9c0a65a726165a7edcba65a226165a7edc7a65a226165cf6db76d5a226165a7edcaa65a226165b7e9c0a65a226165c7f9ca6c299a2165c7f8ca6c299a2165c7f9ba6c299a2165c7f8a96c299a2165a7f9c0a65a7a2165a7f9c0a65a6a2165a77dc929ca5a2165af75c129ca5a2165c7f9c86c2aa65d65c7f8c86c2aa65d65c7f9c66c2aa65d65a7f9c0aaa8865d65a7f9c0a65a825d65c7edca6c89825d65c7eda86c89825d65d76db56c89825d65a7f5cba65a125d65a7f5c8a65a125d65a7f6cc261a125d65a7f5cb261a125d65e775c5261a125d65e7e5c2261a125d65cef5b86d9a125d65e6f5986d9a125d6587fdcbaaa9961d65c7f9ca6c29961d65c7f8ca6c29961d65c7faaa6c29961d65c7f9ba6c29961d65c7dcc96ceaa61965cf5dc56ceaa61965cf5db56ceaa61965a7ddc3aaa9961965c7f8ca6c29961965c7faaa6c29961965d3f9c86c29961965d3f9b86c29961965a7ddc3aa99861965b3f9c0a649861965d3ee996c8986196593fdc8aed976196597f9c0aed976196587fccbaa99761965a7ddc3aa99761965af5dc3aa8a561965c7f9c06ea9921965c7f9ca6c2992196597ddc3aed982196597f9c0aed9821965a5fecc2e5a721965e5f5c12e5a721965a5fdc8a65a721965e5f9c0a65a721965a5fecc661a721965a7f9c0a65a72196597f9c0aed9721965a7bdcba65a421965a7bdc8a65a421965a7bdc7a65a421965e7b9c0a65a421965a7ddc8a65a321965a7ddc7a65a321965e7d9c0a65a321965a7decc661a321965a7decc65da321965a7ddc961da321965a7edc8a65a221965a7edc7a65a221965e7e9c0a65a221965a7eecc661a221965a7f5cba65a121965a7f5c8a65a121965a7f5c7a65a121965e7f1c0a65a121965a7f5c96dda121965aef5c66dda121965a7f6cc65da121965c7f9cba65a021965a7f9c8a65a021965a7f9c7a65a021965a7facc661a021965a7facc65da021965a7f9c961da021965d6f8a96c2995d965dcf9c76c2995d9659eecca6c8985d965d6eca96c8985d965dcedc76c8985d965de6dc56c8985d965de6db56c8985d965c7f8ca6c2995d965 else (if i < 8 then 0xa7decc6e5a321975a7ddcba65a321975a7ddc6a65a321975a7decc6a5a321975e75e99695a321975a7facc6e5a021975a7f9cba65a021975a7f9c8a65a021975a7f9c6a65a021975cdf9b76d5a021975a7facc6a5a021975e5fa9969da021975e77a99695a021975e7ba99691a021975e7da9968da021975e7ea99689a021975e7f299685a02197587fcca6e2999997587fdcba64a8999758fddc32ea8899975a3fdc82a58699975d6ddc3aeda865875b2fdc8aa9a865875d6deaa6cca865875d6dda86cca865875d6f6aa6c4a865875d6f5a86c4a865875d6facc6c0a865875d6faaa6c0a865875d6f9a86c0a865875c7deaa6cca865875c7dda86cca865875d6ddc66cca865875c7f6aa6c4a865875c7f5a86c4a865875c7faaa6c0a865875c7f9a86c0a865875c7ddc36e6aa61875c7ddc96ceaa61875c7ddc3aeda961875e6ddc3aa99661875b6ddc32e19661875b6f5c12e19661875b6f9c02e1966187593fdc8aed9661875a7ddc3aa99661875c7debb6cda921875c7fabb6c1a921875e7b9b46c1a921875e7d9b36c1a921875e7e9b26c1a921875e7f1b16c1a921875a6fccbaa99621875e67ecc659a521875e67dc8659a521875a77ecc659a521875a77dc9619a521875e67d96619a521875a77ecc6a5a521875e75dc36a5a521875e76dc26a5a521875e779c06a5a521875a7decc6e5a321875e6decc659a321875e6ddc8659a321875a7decc659a321875a7ddc9619a321875e6dd96619a321875a7decc6a5a321875e7d9c06a5a321875a7facc6e5a021875e3facc661a021875e3f9c6661a021875a7facc661a021875e6facc659a021875e6f9c8659a021875a7facc659a021875a7f9c9619a021875e3f998619a021875e6f996619a021875a7facc6a5a021875e7b9c46a5a021875e7d9c36a5a021875e7e9c26a5a021875e7f1c16a5a02187587fecc6e4a899875a3fecc2e99899875a3fcca6d9989987587fecc2e998998758fddc32ea8899875b6ddc32e19699875b6f5c12e19699875b6f9c02e19699875a6fccb6a19699875e2fdb86a19699875a6fdcb2a1969987587fdcb2a19699875a6fdc62a1969987587fcca6e5869987597ddc8aeda664c7597ddcaaed8664c75c7ddcaaed8664c7597decc6e98664c75c7debb2e98664c75e3dda86998664c75c7decc6e88664c7597decc6e88664c75c7ddba6988664c75c7ddba6188664c75d75da66d48664c75d75d866d48664c75d75dba6d48664c75d7d9ca6c08664c75d7d9a86c08664c75d7d9a66c08664c75d7d9866c08664c75d7d9ba6c08664c7597ddca2e26664c7597ddc62e26664c75d3dcb86a26664c75d7d9c3aed8664075c7facc6e88664075c7f9ba6188664075d5f9b76188664075d779866d48664075d7b9866d08664075d7d9866cc8664075d7e9866c88664075 else 0xc66e32f1938c7c62e30f17e8bac5b22d11648b185722b61598a9853c2911470a2c50628013c09d44e426f13609a44cc26312d894c4a024812008e0460228112887443421710a084441c20b10188003f01f00f687943c41df0ee07643a21c90e3070c3761b80da86c835e1a70cf867032818c0c205f02e81710b705ac2d01650b1057c2b81590ab054c2a014d0a5051c28814109f04ec27013509904bc258129093047822c113088043420a10207d03dc1e80f107703ac1d00e5071037c1b80d906b034c1960c8062830817e0bc05c82d81660b005682a814e0a4050827813609804581f80f607803a81c80de06703201840bc05b029812c09004502100fc07803901b00cc06002d015009c04802100f006c030015009003c018009003000c000c77db6694a5a6586c7dda76cca5a6586c7dca76cca5a6586c7dda66cca5a6586c7eda86c8a5a6586c7eda76c8a5a6586c7eca76c8a5a6586c7eda66c8a5a6586a7decc6d5a3a6586c7ddb76d5a3a6586a7ddc72d5a3a6586a7ddc62d5a3a6586e75db52d5a3a6586e75cb5695a3a6586a7ddc7295a3a6586a7ddc6295a3a6586e75db5295a3a6586b7cdc2295a3a6586eaddb86d9a3a6586eaddb8699a3a6586ceddc66ceaa65586cbf9c86c2aa65586c7dcca6ce9965586d75dc56ce9965586a7ddc3aa99765586a7f9c0aa99765586a7ddc3a65a72558697ddc3aed972558697edc2aed9725586c7ddc36e6aa61886c7ddc96ceaa61886d75dc66cca765486d779c86c0a765486d779c66c0a765486977dc7aed8665486d75dc3aed8665486977ecc2e98665486977dc72e98665486b75dc329d8665486b76dc229d8665486b779c029d866548697ddc3aed8665486d75dc96cca765486d779c96c0a765486b57ecc2e99765486f47dc62e99765486f55dc32e99765486f579c02e99765486b57ecc6d59765486c7ddcaaed8664c8697ddc5aed8664c8697ddc7aeda564c86b75dc7aed9564c86b75ecc6dd9564c8697ddc7aed9564c8697f9c5aeda76408697facc6e1a76408697f9c7aed866408697f9c5aed8664086d7d9c3aed866408697f9c7aeda56408697facc6e1a564086c7f9b869da564086b5f9c5aed9764086b5facc6d5976408697f9c5aed9764086b779c7aed9564086b77acc6dd956408697f9c7aed9564086c7decc6cca9a2266c7ddc56cca9a2266c7dcc56cca9a2266c7ddb56cca9a2266c7dcb56cca9a2266c3fda86dc9825666a7eecc261a225666a7edcb261a225666e3edb8261a225666a7edc7261a225666a7edcb25da225666a7edc825da225666e5edb725da225666c7ddc32e6aa61975c7ddc96ceaa61975c7dcc96ceaa61975c7ddb96ceaa61975a7ddc3aa9a96197587fdcbaaa9961975a7ddc3aaa9961975a7ddc32a69921975a7f9c02a69921975e57e9969da521975)) else (if i < 10 then 0x161730ad850c25611307d838c1960b304d820c0d605301d808c015ff2fed7f0bf55f92fbd7d8be95f32f8d7c0bdd5ed2f5d7a8bd15e72f2d790bc55e12efd778bb95db2ecd760bad5d52e9d748ba15cf2e6d730b955c92e3d718b895c32e0d700b7d5bd2ddd6e8b715b72dad6d0b655b12d7d6b8b595ab2d4d6a0b4d5a52d1d688b4159f2ced670b355992cbd658b295932c8d640b1d58d2c5d628b115872c2d610b055812bfd5f8af957b2bcd5e0aed5752b9d5c8ae156f2b6d5b0ad55692b3d598ac95632b0d580abd55d2add568ab15572aad550aa55512a7d538a9954b2a4d520a8d5452a1d508a8153f29ed4f0a7553929bd4d8a69533298d4c0a5d52d295d4a8a51527292d490a4552128fd478a3951b28cd460a2d515289d448a2150f286d430a15509283d418a09503280d4009fd4fd27dd3e89f14f727ad3d09e54f1277d3b89d94eb274d3a09cd4e5271d3889c14df26ed3709b54d926bd3589a94d3268d34099d4cd265d3289914c7262d3109854c125fd2f89794bb25cd2e096d4b5259d2c89614af256d2b09554a9253d2989494a3250d28093d49d24dd26893149724ad250925491247d23891948b244d22090d485241d20890147f23ed1f08f547923bd1d88e9473238d1c08dd46d235d1a88d1467232d1908c546122fd1788b945b22cd1608ad455229d1488a144f226d130895449223d118889443220d10087d43d21dd0e887143721ad0d0865431217d0b885942b214d0a084d425211d08884141f20ed07083541920bd058829413208d04081d40d205d028811407202d0108054011ffcff87f93fb1fccfe07ed3f51f9cfc87e13ef1f6cfb07d53e91f3cf987c93e31f0cf807bd3dd1edcf687b13d71eacf507a53d11e7cf387993cb1e4cf2078d3c51e1cf087813bf1decef07753b91dbced87693b31d8cec075d3ad1d5cea87513a71d2ce907453a11cfce7873939b1ccce6072d3951c9ce4872138f1c6ce307153891c3ce187093831c0ce006fd37d1bc8dde6ce3659b20d8a6bd35a9ab4d4a69d34d1a5cd286913471a2cd1068534119e8cee67433899b8cd66683329988cbe65c32c9958ca664b3241914c7a63531698a8c4461a3091828c045fa2fb97d0be25ee2f31778bb65d82ea9734b8a5c22df96f0b725b62d71698b465a02ce9668b2e5942c89638b165882c295f4af45772ba15c4adc5662af156caa654b2a41514a7a53a29914a8a4451a28b9450a2250e2859420a0a50227f93f09f24f627993ac9c64db269932c9864bb259927093249624992408e846c23491848b2456229912c88644021e90e886e43421890b885642320d904c8164082000fe07e03e81f28f887b43d21e78f307883bc1dc8ed87663b01d40e8073a39a1cb8e5072238e1c30df86f63781ba8dc86de36c1b20d706b23561a98d4069a34a1a38cf else (if i < 11 then 0xf82103e498d63f8be1f82680001e005e005e004e004e0040820820820000f80182000000000002082083e004003e005e007e0040f001f001f001f0017001f8010200007821780100081e005e00400200203801380100082080080000003450408208207801780181e005e084001c5060580158015801580100000002082082000083a007a005a007a007a007a006a007e007101a3e2f804020020f93e2f87e02425782101e005e006080e004e004080082002003600760076005600406801a801680168010006801680182068016801020800682168010008208206801680100080082068016801020020020832007200720072007200720072007e3f804f0fe3f80130fe3d8be08f62076204004fe48808013f92204e104fe48a08160060234180000000003078707040c1c123e1e801e801680101a00400000200305860f901782103e006000003e007a404080e0040000016007e0040f801f801f801f8017801000000000000020000820020000000000820020f001f00100002e0040780100000000000000000003c0040000000020000000000000000d87e08b61f82280000001e004000001600560040000000000000000000000000000000000000fcd7e53f1df88fc17df3eedf70fb57d93ebdf58fa97d33e8df40f9d7cd3e5df28f917c73e2df10f857c13dfdef8f797bb3dcdee0f6d7b53d9dec8f617af3d6deb0f557a93d3de98f497a33d0de80f3d79d3cdde68f317973cade50f257913c7de38f1978b3c4de20f0d7853c1de08f0177f3beddf0ef57793bbddd8ee97733b8ddc0edd76d3b5dda8ed17673b2dd90ec57613afdd78eb975b3acdd60ead7553a9dd48ea174f3a6dd30e957493a3dd18e897433a0dd00e7d73d39ddce8e7173739adcd0e65731397dcb8e5972b394dca0e4d725391dc88e4171f38edc70e3571938bdc58e29713388dc40e1d70d385dc28e11707382dc10e0570137fdbf8df96fb37cdbe0ded6f5379dbc8de16ef376dbb0dd56e9373db98dc96e3370db80dbd6dd36ddb68db16d736adb50da56d1367db38d996cb364db20d8d6c5361db08d816bf35edaf0d756b935bdad8d696b3358dac0d5d6ad355daa8d516a7352da90d456a134fda78d3969b34cda60d2d695349da48d2168f346da30d15689343da18d09683340da00cfd67d33dd9e8cf167733ad9d0ce5671337d9b8cd966b334d9a0ccd665331d988cc165f32ed970cb565932bd958ca9653328d940c9d64d325d928c91647322d910c8564131fd8f8c7963b31cd8e0c6d635319d8c8c6162f316d8b0c55629313d898c49623310d880c3d61d30dd868c3 else 0x0))))
def lay511r9 : Packing := (1116,5,5,63,0,13,1,word511r9)
def keys511k10 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0x961b3b41a4c11ce0b480ed421bfc100e05ea02550615040e82f26040e1c808e6f2373c07171e2e8187e1f1e45721d35883282c9ec2ed132d050db198b11711eaa0985c12040ddf0674913f21b6000021a4000008389e28bf1fa5897561a20000410b80003c66da2a10022261d3916e000000007883b80d8000021ac48ec8420d096a60dbd8d30c1c80000716e0000105a4e83234ae3a3128450215928140105bc50a98d0000078e4c447d02d70000000024853422c906f8441ac5fe0000796d4066db58de255247358d19a1f5021fd441287730223201f8005604cd800fc455c03340c0b17da7bba10135072045798418000018cee6082038f683f98cbc0000c8db21a3c86d00001407f9940990b306b9c1e5d124a8d05b0782059a00bdd0cb7213e2fc004fe02a00001d950c4c4e0a271592e05bf179705e9229ca146f007b049910619130c10e10f8cc82be0a9006a00a5c00000000000000001d211e8d110ad800038090a043f158887c40001603790a7c2160879aa36b25e730c340000621ef0a90000344340000f11369168000164480000306440001991a000078ef2c143e3a78048e0bbc86b5c0ab00000ae7650ad407800000000106ff819c1225385c8e5f27089b21c386d892040000000000000000020e920e13ae49d78470dca206b08060134b0c600005054602c6e08eb0370e35882dd81e1d0d1505610487004c1102303284612617f18d28000245b00000000068604000050e6000b0203220b19000c0701091007061705120408161400010003330006190e040002310305000000120f00240b33001223250f30000b0827200013210d0000021b0a0000381700030a30170101000100040815010015101a00060601010100040c100602070000000300014c25160c00050d091a020f020300000307010100270407120502001d0600040307570000312205060602000015091a010613051f05000b000266060003692304040604022f0805060411072d022709001e0701000a01431416022b821200352109260009020200001c0007000b01023969000a0423010002050112790401284d00043003100d0025000d02020200020c202202010524031e0d1d08000d190200050900132600001d0115061b2b0a241200031a0102090200030b01000776060c042501130612060207020100033d12084b14120459240d140113000020282c0e0c0501022902240400003d00022b01050f0c08140b00192408110d01025509180000070702002f0000000001090c15061b0a0f060004050b060f00041a0401060400000b000316000101010a000230070905033b19010019000104000000002500000006170000201e2c0400010000083a08071408050301270001000400048e0509010202004e121c042b0200000500020000021e043e03000018 else 0x1c8b211e1a011946a0c362918cf417c285389ce708b00002c188042b318a00948000022e6d21e00003c6e8c2cf70c36c491c67ee443aa09585ec02840047fd761017fc15461801004e8ad252a0b8e8718f489d244890321c065f0b0e0231586f0094f2ea741ed2446416a78c6dc7c240a280ea69018e1f8c306903c944a0c0c1626401355819780da823dc80b40d09039fe2bad08ec42c7c3e7e098000040596c2c4819840c12a2d90448000020f780002058e104961bd2109ce15be0d900f620053c3c5805a51f6526fd876fa11312105036d13812216a04f6c3d4c1a2e230000058f600001813df04ea0b4cc293a3ab41f99821f082942e7717eb0413471c6030521880002c34002c8f940500898375e1e6f0dc001a9f19aa2fac1ca782e94038613ba08bce0eea5bdc258dc29f8293106b018520ff0892f21d96112f193930b1c2f04139b0ebe6571c64b88502064a0160c27598cff1648000342da02e15c5e000000001093d000000001c82e0000000050676c1f402ae5ca950bd8000043b5959dd66acc7b4000000007cb8e07120000e081000000000b8c800001833ea2a0902d00006c0d187c00000206aa0115c0ade076382cea32555b242ed0000210728294e1d200006829d0216a2f71ca8d0e83a265806b9196103cf0752a0c800007838241cc814cd1bde8828000000005d6df057503b02084a15cf88d64625808ab0633883447fe0242e1f5d0862077352c5321200003c26123df618e7e40e57a4eb6dbde74c13046dfe0c300005035e033ee2f380d4c09040001e298000068db79879e3b6a89024ee9c5be226d80e8d8f480001a184556fa415502a643d4f1c672d53c38cc292a015209c3019b20dc040df0728c019614ee14a705df51f040e105e1a0dfac6cbe409f16b42028165c63a5008450a9ff6a6b12ba14fb62d3c8a5c28ad56dcca088407420904aa000ef60a18855719ca0ea8d11a23b4841df04e1035ac107f1ecea6f68326cba7a01eb05bcd223d2d8a20260ba12252e31f71946006f01020301309f490d3c32b894bc1e318369f1b1024c5ca7d0ecf62340000306b0091fa09cb8c1215248793c382a33a121ebe365080f20203c7392743d0c250d6f0abd057ac70f20d85575585580898439fb014205f943500168316efa6ea041fab94f19e80000000059a4b025889a3412bc12fd000800004465c002813cfa41581e0a1d910fd50c5c0105c32671f8d867b618a00006062d0c1322b220150000008940000e010e04e289b3c3d7a114000048407b21da096d836b471786a44458fc40485f188147440dc6530e48d8982299b1d148ff604f000001159c0fc80860000061fc000000000a0fb706610f44c1c40000a0a2010d781f3413fe195000000000694ae063a06424347a18bfa0a80816575043c4003bc0ce1c05) else (if i < 3 then 0xe240e05c80bb00031e43a057090b93c5ebe02d702f5a3510046e3c2384e58b64e2396093781ab0e69a610000031a73a0df12a2019421a6e88b4588e30e8805ee8efe40de0000143069109c6618222a47f71138021983f7415f190a0217d40f5e8ad34377c55a00000000410a90630e18ed1b954b66a02b82cd807780003c5340000000030efb062a0000000050e5984b7c22e71d8f086c0001e397189736399c7ba641fe19b9256400000000d0fe800010692a34a00001c3ee84c0e3606029c10785195e229204a6c0fb0495c0b1f09720e17a185f2f000002098d0666e0b714e5e889c07a7411090e49631660a6601130256c378d1bd8910511c40cb4c5d27ab1d211c417743ff427cace8083b28167883c3135f8b0212d0e214316dc442a205263efc02ef239e903d444571c0d80d74872a160f19f690cec417790806286c3af50b2002e2188882b4815d20fd00ead0d46916b0413e02b92ff406dd207eb14db84f0d2da102bb0e9f830412906140c210c8d5d6100a01d0133b8f3044ae22b2c8190000155dfe45b90c680001825883a43155e07aa0704622ab05a30eb800014450f818cc69db204211b3018a05a5804864569222000000001212410c7a07d206e220060000422e84132a0eec154985ce05840000612692b6a80a96880e00cea57fc4f7607cb137000eaf8596100f165bc71002cf2000441780000000148c681244862540cf20b0d0216899b8250c35f262da8ef487aee82d10da98aabc70812c43168a05d2c50f0b97e1655804a034f80a0205b402ffc0c7b10f00a862458000143ba2060588ccc264aa7908584a43ab1a3b1c30223aa216217f21fb916610b8871b74375000054302873102a8c148f90448761e3e8d21b5081bc40ea0fe60e6901ec00010c584225d03e285e2408dd12318c58e177e35601a7d80cf044721fcc05e582ec83ee314da047c03f0868a2afc512a380a6051b40b811af10e1ac2ead04aa93f320a002cde07331b0b88efc3c7843b94465015603c1838dd8ae0000383ac0000000078c880001e0d330fc1244f00f464410000000000000000000003102e025780a621ad80e7044d3a2b0485938fa51171a42d2217e8224c7d58148211068ebd4732822b821348df565f1c379e15c063968697a00830320afb88783225130bb10bd291a660507110d2354838b03ad308d104c446d1090900c958417467881ccb41cb916483078359c1dc1acbf435d93ceb4f628685456a20413198d084aa21883f0000028ab380ea838bd13e982fb5167b05829e1f079f46348051d58800c2c46d2e21da47ed00380000000080695c2f502c243fa00004d0fdc29bc296515db0481c1d5eba00000380e4000163f5b10980002c7f2e25aa01a386b181fea364e1f3ecb75881c000090868000084ff8086342a5c3df453bc262a168 else 0x2485c0000c93b80002053de82c3211106fd71afa2a5c87a180ca04e2c85c6576184840001244940c6306f7f19d2283000048eef54f9a8d9c1844630f033363cafa09c10160834d081a09114135c254227a411ca05af46e1232e6175a457b4354e37384a9d44bc0000e0e8946e88a8000000000c47e5c071a4d20000e147382c800e9e068a15e9828c30a04295120120b8180078367c97678221c1078329c13970db1d21e81de70a0d0c330478a2d52075f09cc07c593c4f1a039067426fc37700006a563428a430a7129bcb9543db305bf85e7825dc8a2694050cb8865bc0a5f87f70aac2b804468838081c8c01c38214e004e056707d4855f41c071fe323ea06cde12368561440647b8812d011b720bb426a83347182f0a3cc72a21af50529009d41e4238840ad70c00000040de000060c75c3b5c200e0e380f9b21ec6453a117a26cb464180e7b472689434092e40c648f5abb80001f0c700000632fc239c4010017e8628048bc37800f900000000000000000306940000c188c20450f2543f2000020f4c08c603b7c005915b800000001e915121f00000000000000000682011398c432796db00ac0001810ef02778a8802d82332081c00002927e830380af80d75c6572170317522586624e410f90d880f3c010ae18701fdb084644bc08b9001fc0a190070a219f02e00843028fd03d6071c8c38c79003f64151c26f9339ca843214860cd7c2a9636331b5280f0f3590ad7f0eeb415d44b8838381edb8df3110c441d311d4aeebc3ed4b0fe00d2018886abc28ce13a8882040d318c9b47d9e319082182a6f09b06154804341715584604d2403d28c8f03968231d5f7c0af20ddc022f442bc16af1f2c0bf901e923a10ca620137c714e0b5715f80001423e000051a20c36086466313b16740958000190e5d072800014348c1e83212feb17c4bf024e04741093f8780012700004a37c0000615c000074495c7580000c81980002402c00000000640a882324307111fd802c92340000620da8d0cf20f228400007900e806c0000000000001c8240000000020668c297032481ef707b8009f83e4707880001e2b042b6ca1600001036478d5013b00003e15ce259820078f5b83bee3d064dcc8a4f0538a07d000041151d1a5009b108f4214841ee6b3c05cf10f1de19541bcc207885f4000082c100000c6d60510c2026084be53bc07ca3a361e5d22d1c24b31c02137fa1fc00014092a11b80002822a0013c426287c0879c095290d84803651f31414c47748ddac34c43fe20686412e489a))
def cut511k9p0 (i : Nat) : Nat := 0x80904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000808840000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904
def cut511k9p363 (i : Nat) : Nat := 0x822100000000000010120000000000009050000000000000101100000000000060280000000000002108800000000000210880000000000021088000000000006028000000000000016080000000000082210000000000008221000000000000822100000000000082210000000000008221000000000000822100000000000082210000000000009008800000000000032100000000000080904000000000008090400000000000409040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000004090400000000000c0b0400000000000c0b0400000000000409040000000000040904000000000004090400000000000809040000000000000b04000000000008221000000000000005000000000000000500000000000008090400000000000822100000000000090088000000000000321000000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000009219000000000000921900000000000040904
def cut511k9p427 (i : Nat) : Nat := 0x8090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000000500000000000000050000000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000005000000000000090084000000000006010400000000000601100000000000002904000000000002108800000000000809040000000000092190000000000008010400000000000921900000000000092190000000000009219000000000000921900000000000080904000000000009219000000000000921900000000000092190000000000002108800000000000101100000000000021088000000000002108800000000000c0b0400000000000210880000000000021088000000000002108800000000000210880000000000080884000000000009219000000000000921900000000000092190000000000002108800000000000210880000000000040904000000000008088400000000000808840000000000080884000000000008088400000000000409040000000000080884000000000002108800000000000210880000000000021088000000000004088400000000000210880000000000021088
def cut511k9p491 (i : Nat) : Nat := 0x80904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000005000000000000000500000000000000050000000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000049040000000000080904
def cut511k9p555 (i : Nat) : Nat := 0x301200000000000080904000000000000052000000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008088400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000021088000000000008090400000000000809040000000000040884000000000008090400000000000809040000000000080904000000000008090400000000000822100000000000080884000000000004088400000000000408840000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000004088400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000000500
def cut511k9p608 (i : Nat) : Nat := 0x111040220200850211104022020085021110402202008502111040220200864211104022020084c211104022020084c211104022020084c211104022020084e611104022020085021110402202008502111040220200850211104022020085021110402202008502111040220200850210910800112104161091080001210656109108001121041610910800112104161110402202108502111040020210852642084408002a81921110402202108542111040220210854211104022021085c211104022021085021110402202108502111040220210851e1092080011410416109108001121041a20a804001600841220a100840409114a20a100040409116620a1008404091146109108001121041a1091080011010416111040260210852220a1008404091146109108001121061648088c080292825211104022021085421110402202108542111040220210854220a1008404091146111040220210850211104022021085021110402202108502222410004282109e20a1008404011146111040020210852220a10084040111461110400202108522111040020210852620a100840409114620a1008404091146242100840401114a111040020210852611104022061085261110400202108526111040020210852611104002021085261110400202108526111040220210854211104002021085261110400202108526
def cut511k9p672 (i : Nat) : Nat := 0x48088c0c0292821a222410000282125610a111028829215e11241806029281d248088c0c0292825e11241806029281d211241806029281d211241806029281d211241806029281d211241806029281d210a11102882921621110402202108502111050220210854211104022021085221110402202108522109108001121041642084408002a81921110402202108502111040220210850211104022021085021110402202108542109108001121041610910800112104161091080011210416109108001101041611104022029085021091080011210416109108001101041620a10084040911461110402202108542109108001121041a1091080011010416111040220210850210910800112104161110402202108502109108001121041611104022021085021110402202108502111040220210850211104022021085021110402202108502111040220210850211104022021085021110402202108502109108001121041611104023029084e211104026021084e211104022029085021110402206108502109108001121041211104022021084e611104022029085021091080011210416109108001101041210910800112104161110402202108502111040220210850211104022021085021110402202108502109108001121041a1110402202008502111040220200850211104022020085021110402202008502
def cut511k9p736 (i : Nat) : Nat := 0x11104002021084e61110402202108502111040220210850211104002021084e61110402202108502111040220210850211105022021085021110402202108502111040220210850211104002021084e6111040220210850211104022021085021110402202108502111040220210850211104002021084e6111040620210850220a100c4040911c61110402202108502111040020210852611104022021085221110402202108522111040220210852211104022021085221110502202108522111040020210852220c211040c01218a48088c0c02928152111040220210850248088c0c029282521124180602928252112418060292825220a1008404011146109108000121061610c0804208008902111040020210852211104022021085021110402202108502111040020210852610910810110104161091080011010416111040220210850211104022021085021110402202108502109108001121041611104022021085021110402202108502114220002104085a2224100002821256109108001121041610910800112104161091080001210656114220002104085e1091080001210656109108001121041a1110402202108642222410004282105620a100c404191186224204040921212610c211040809218a111040220210860211241806029281d248088c0c0292825e11241806029281d210a111028829215e
def cut511k9p800 (i : Nat) : Nat := 0x1110402202108502111040220210850210c080c2082889c6111040220210850211104002021084e6111040020210852220a10084040111461110400202108522222810004302105a111040020210852611104002021085261110502202108602222410006292105620a100840409114611104002021085221110400602108522111040020210852611104002021085261110402202108502111040220210850211104022021086421110402202108502111040220210850211104022021085021110402202108502111040220210864211104022021084c220a100c4041911c6111060220210850211104022021085421110401206108522111040020210852211104002021085221110400202108522109108001121041610a11002002a81d610a11002002a81d610910800112104162421008404411146109108000121061620a120840c011146111040020210852210910810112104161110400202108526111040220210850211104022021085421110400202108526109108001121041a109108081121041610a11002002a81d6111040020210852620a1008404011146111040220210850211104002021085261110402202108542111040220210850211104022021085421110400202108526111040220210854211104002021085261110400202108526111040220210850211104022021085021110402202108502
def cut511k9p864 (i : Nat) : Nat := 0x111040220210854211104022021085421110402202108542109108001121041610910800112104161091080011210416109108001121041610910800112104161110402202108502111040220210850211104022021085021110402202108502111040220210850211104022021086021110402202108602111040220210860220a100840409110611104022021084e211104022021084e211104022021084e211104022021084e211104022021085021110402202108502111040220210850210910800112105d211104022021085221110402202108526111040220210851e111040220210861e11104022021084de11104022021084de11104022021084de11104022021084de11104022021085221110400202108522111040020210852220a1008404011146111040020210852211104002021085221110400202108522111040020210852220a1008404011146111040020210852220a10084040111461110400202108522111040020210851e1110400202108522111040020210851e11104022021085021110402202108502111040220210850220a100840401114620a100840401114611104002021085221110400602108522111040220210850211104022021085021110402202108502109208001141041611104022021085021110402202108502109108001121041611104002021085221110400202108526
def cut511k9p928 (i : Nat) : Nat := 0x11104022021085021091080011210416111040220210850210910800112106161110402202108522109108001121041610910800112104161091080011210416109108001121041e111040220210850211104022021085021110402202108526109108101921041a114220002104085e1110402202108502111040220210852211104022021084e211104022021084e211104022021084e211104022021084e21110402202108542109108001121042211104022021085c21091080011210416111040220210860211104022021085c2111040220210860211104022021085c211104022021085c211104022021085e6111040220210850210910800112104221110402202108502109108001121041611104022021085021110402202108502111040220210850211104022021084e61110402202108522111040220210851e111040220210851e111040220210852210910800112105e2111040220210851e10910800112106161110402202108522111040220210851e111040220210851e111040220210852211104022021084de11104022021084de11104022021084de11104022021084de111040220210854211104022021085421110402202108542111040220210854210910800112104161091080011210422109108001121042210910800112106621110402202108542109108101921041e1110402202108542
def cut511k9p992 (i : Nat) : Nat := 0x1110402202108522111040220210852210910c0011210616111040220210851e111040220210851e1110402202108522111040220210861e111040220210861e111040220210852210920810110104161091080011210416109108001121041610910800112104161091080011210416109108001121041a109108001101041610910800110104161091080011010416109108001101041610910800110104161091080011010416109108001101041610910800112104161091080011210416109108001121041610910800112104161091080811210416111040220210854242084408002a81921110402202108502111040220210852611104022021085c211104022021085021110402202108502111040220210850211104022021085021110402202108602111040220210852220a10084040911461110402202108522111040220210852210910c00112106561110402202108522111040220210851e111040220210861e11104022021084de11104022021084de11104022021084de11104022021084de111040220210854211104022021085421091080011210416109108101921041a109108001121041e109108101921041e109108001121041e1110402202108502109108001121041e11104022021085021110402202108522109108001121061e111040220210852210910800112104161110402202108502
def cut511k9p1056 (i : Nat) : Nat := 0x222410004382109a1091080011210416109108001121041610910800112104161091080011010416109108001101041610910800110104161091080011010416109208101101041610910800112104161091080011210416114220002104085e109108001121041210910800112104121091080011210416114220002104085e10910800112104121091080011010412109108001121041a109108001121041a111040220210850220a120840c09114610910800112104161091081011210412111040220210850211104002021085261091080011210416109108001121041610910800110104161091080011210416109108001121041611104022021085c220a100840409110611104026021085e2111040220610860210910800112104121110402202108602111040220210860211104022021085c211104022021085c211104022021085e6109108001121041611104022021085c220a100840409110611104022021085c21110402202108582111040220210858211104022021085a611104022021085c2109108001121041610910800112104161110402202108502111040220210860211104022021086021110402202108502109108001121061611104022021085221110402206108522109108001121061610910800112105d2
def word511r10 (i : Nat) : Nat := (if i < 11 then (if i < 5 then (if i < 2 then (if i < 1 then 0x618861d756ec3346430ebb1f698a65d4759afb74432ea3ad57db9219751d6eaed990cba8eb75e6c0865d475d8fd55332ea3af87e88999751d796ec310cc98ebcbe6188664075d5bb0cd190cb2eaf9866808659733f4c94cc2acb39f2e97661565e4f9313330ab2ee79b0aa965196f3cd8554b28cba9f6a0a859465d4fd55442ca32ec7da729d65196b3edc90eb28cbc6f61c8765065b4fd76c310d2aea7eaa6188695793ed4b0c434abe1f69d8621a55f0fceec310d2afa5d8668c86957d36c3344434abe9e619a021a55b8f96cc3aed2adc7ebb5d87695753ed4151334abb1f69ca799a55f0fb0e43ccd2aeadd8668c8695637edcd54c310d5d76cca765486aedb6453b2a435779b029d9521b2bf5532eca90d5b7aed8664c86aebd76cab264353fabb6199021aafd5db2ec810d5deaed9564086b4f96ad4d11335addb32a68899a7775db444accdabba21a2256668fbb6654d11334eddb3aa98699a73f5db4a434cda9fa21a521a66d5bd10d190d334ef6bb6848699b57d44340434cd5b76cca865875adeb625432c3ad6f9b02a1961d733ecb34a430eb9b7659a321875c7f330d010c3ae6f996680861d697f5db31330eb8bf6a688998758fbb74433263ad75db5219931d6becd810cc98eb9b7aaa6664c75e5bd11333263ac7f9ba219901d6afcdb90cc80eb5de6d48664075af7368433203ad7d9b3219901d6bf4d910cc80eb5fc6c48664075e5f511333203ac7ddb3aa9985963fcd8554cc2cb1fbaeda226165a7f3614cd10b2c7f9b0aa9975969f6d9130c32cb5bb6c89899965f0fb0ebb30ab2c77db9aa9651971df55510ca0cb5ee6c08765065cd7d553332832f2be88999941967bb5db424b4abb5d9dda125a559ebb675530d2ac77cb9aa8869566bedb952434ab3d76cca921a559edb645490d2acf79b02a4869566bf5db4e434ab95f6a5a721a559ebd76d190d2aed5e7768c8695772ec3346434ab9d76a5a321a55dabb4ed190d2acf6ebb688869575b6c3344434ab9db6a5a221a55dadb4ed110d2aef2da4688869577a6d1b44434ab3deaeda021a55daf4eed010d2aeb7986680869573bcd4b40434abb5e69da021a55de7348d010d2aef59a3680869577b4d1340434abbdc685a021a559edb65552ed2acf79b02a1769566be5d30ebb4ab3ddaeda11da55bcf36054ccd2ade79b026266956f3cd814f334ab79e6c08799a55f0fd113bccd2ade75b125a66956e3edb90d334ab78f6d08699a55bcbb66434cd2ade6db221a66956f3ad890d334ab79e6c08699a55bceb623b4cd2ac7f6bb684969572fb3bb424b4ab5be6c0a999a55adf3604c4cd2ac7f9b02a6669567bcd8554b2cab3db6c8a859655e0fb2ec332a4362deaa6199321b92ec332ac990dc9e6199564086e5730cca3204372d98664d9021b978c3322c810da97619a321a55 else 0xab3f7aeda321a55dbbceed190d2aeedd8668c869577aedab46434abb7769da321a55debb4ad190d2acfeebb688869576f73bb44434abafb619a221a55dedb6ad110d2aededa7688869577b6d2b44434abbeb691a221a55df9b46d110d2acffabb680869576fd3bb40434abafe619a021a55def36ad010d2aedf9a7680869577bcd2b40434abbee691a021a55dfb346d010d2aefe9a2680869577f8d0b40434ab3fb6caaa5da558ffb7054aed2acff9b02a176956bfcd8130bb4ab37f2e9875da55cdfd544b2ed2af4fd87259769563fedd1303b4ab8ff6a0981da55aff3604c0ed2acff6bb684769573fa4c3423b4abbdd6d5a11da55adfb7054ccd2ad6fdb72a666957b7cd8153334ab5bf2e5a899a55bcfb6a544cd2ad6fdb72626695797e54d11334ab5bf2e5a799a55cdf952d3ccd2ade7db529e66956f7cd814f334ab5bf2e58799a55e5f930c3ccd2ade7db521e66956f7cd810f334abd3f2a67799a55e9f9313bccd2af8fe889de66956b7e5ccef334ab79f2e1a599a55f4fd10d2ccd2afc7e77696669563fedc153334ab5fe6c0a999a55adfb6c4c4cd2ad7f9b0262669571fe54d11334ab97f2a67799a55adf972c34cd2adcfdb721a66956f3eda90d334ab7af6d08699a55bdbb66434cd2adeedb221a66956f7ad890d334ab7be6c08699a55adf972bb4cd2ae6fca95da66956f3eda8ed334ab7bd6c47699a55d6fd10d2ccd2aed7e776966695773ebb34b334ab3df6daaa5d6559efb70532eb2aed7e77299759567be5d30cbacab75f6dc865d655bebb66432eb2adf6db221975956fbcd810cbacabb9f299765d655dcf975332eb2aee7eaa9997595773e544ccbacabe9fa22665d655f8fcef332eb2acf7cba999759567bedc554b2cab3df6deaa596559efb6e542cb2adf6db22a1659575be5d510b2cabadfaaa8859655e6f973442cb2acf7cbaa21659575bf4434eb2cab7dd6c4a7596559ef974c3acb2ade7db621d65956fbcd810eb2cabb5f2ea7759655dafd553bacb2aed7da89dd659576be544eeb2cabe5fa227759655f8f96d3bacb2acf7cba9dd659576bed3ceeb2cab79f2da7759655d6f950c32cb2add7db721965956f9eda10cb2cab7d76cc8659655bedb64432cb2adf75b121965956fbcd810cb2cab79faed7659655dcfd54bb2cb2af67cb95d965957d3f442ecb2cabf1f29d7659655f8fb0ebb2cb2afc7e775d965956fbad88ecb2cabb9f6a26659655dcf951332cb2afa7e8899965956f3edbcccb2cabb9f69e6659655f8fcef332cb2aeaddb3aa98621ad6ed9d54c310da9f694a561886cafb4e53b2a436a7eaa6199521b87ecbb0cca90dcb7619a564c86e5bb0ccab264372f9866559021b17ed4953444cdc9fa219525666c5fb30d35113352fcb9a208699b56ec3346432eb8bf6a0a865875a5fb72c310c3ae2fda9) else (if i < 3 then 0x553bb0d2aed7ca99dd86956fbad892cc34ab3df6dca921a55dafd76d390d2aed7cb969c869567bf5db4e434ab75faeda721a55cefb52d390d2acf7dba25c869576bed392e434abb5faaa7721a55eafb533b90d2aed7ca99dc86956f3f5db0c434abf1f9dd8621a55dafb4ec310d2aef5db768c869577ae4bb46434abbd7619a321a55debb4ed190d2afd5e7768c869577b6dbb44434abbdb25da221a55dedb0cd110d2aef6da7688869577bcdbb40434abbde25da021a55def30cd010d2aef79a768086957ebd3bb40434ab3df6e2aa5da55dafb6f552ed2aef6db2aa976956fb6d9554bb4ab3df6e0a95da559efd76d42ed2aeb7da82a176956fbcd8150bb4ab3df6e8985da55bafb6e4c2ed2adf79b0261769576bf5530ebb4abf1f2d9875da559ef974c3aed2ade7cb661d7695773f5512cbb4abf1f61c965da55fceb624b2ed2adf75b1259769567bedd30cbb4abadf2a1865da55bafb6e432ed2adf3db421976956faed990cbb4ab7db6c8865da55beeb62432ed2adf79b0219769567bf5db503b4ab3df6e8981da55d6fb504c0ed2adf79b026076956ebf5daec3b4abb5f6a1761da55deeb70d08ed2aef7498684769577bac33423b4ab79f6e0a999a55bcfb6e54ccd2afe79b02a666956f3e5cb51334abb9f6a0a899a55bcfb6e544cd2ade7cba26266956f3edb931334abf9e6c09899a55f4fb75444cd2afa7cbaa2266957d3e54d11334ab79f2e5a799a55dcf952d3ccd2ade7cb869e66957d3f4434f334ab79f6e0a799a55f4fd1053ccd2ade7db825e66957d3f4412f334ab79faed8799a55bcf974c3ccd2ade7cb961e66957d3e4c30f334abf1f29d8799a55f8fb0e43ccd2afc7cb99de66957e3e54cef334abf1f6a27799a55f8f9513bccd2afc7c989de66956fbcd8153334ab3df6dca899a559efb6c544cd2ade7db62a266956f3edb131334ab7de6c09899a55f4fb6d444cd2afa7cb6a22669567be5d511334ab79f6da8899a55d6fd10d3ccd2ade7db629e66956fbcd814f334ab79f6d89799a559ef974c3ccd2ade7db621e66956fbcd810f334abb5f6a27799a55daf9513bccd2af97e889de66956f3edc12d334abe9fa209699a55bcfb6e4b4cd2afc7e7725a66956f3f5db0d334ab79f2e98699a55bcf972c34cd2afa7e8861a66957e3f3bb0d334abe9fa208699a55bcfb6e434cd2afc7e7721a66956f3e5caed334ab79f6e17699a55bcf970bb4cd2afa7e885da66957e3ec3aed334ab79f6e07699a55f4fd103b4cd2add7db529a77956ededa14d3bcab1ff6d8a99de558ffd76d412d2ae5fda89dc969573fb5db424b4ab9fd6e1a125a55cfe970d092d2ae7f5b7684969573fa5bb424b4ab9fd9dda125a559fbb675530d2ae5fca99dd869566ff5db4e434ab97f2e5a721a55dafb6ad390d2aed7e77694869576bed3b4a434 else (if i < 4 then 0x55973be5492ec2acb6df6e09761565beeb624bb0ab2de7ebb29985596f3edb94cc2acbf8f6d0a661565be7b685330ab2dd7db721985596faed990cc2acb7db6c88661565bef3604330ab2de7ebb5d985596f3e5d2ecc2acbb9f2e97661565dcfd54bb30ab2ee7ca95d985597b3f4caecc2acbe9f2617661565f8f92ebb30ab2cf7cba5d985597cbec3aecc2acb79f2ea6661565dcfd553330ab2f67ca999985597d3e4c4ccc2acbe9fa226661565bcfb6f3330ab2fa7d879998559677edb94cc2acb3bf2e97661565f1fb0ebb30ab2cefcba9998559737ed4cccc2acbcbf2626661565afdb644c2eab2e3fda9a217559757f4414cbaacb3bf2ea665d565cdfb53332eab2e5fda729d98196bfcd814ecc0cb1ffaeda666065a7fb7253d1032dbf5b129e881971fecc34f440cb1ff6e2aa65c65aff3605432e32e3fcbaa21971971ff55510cb8cbc7f2de8865c658ff9754432e32c7fdb9aa9871967deda554c38cb4ffaed9861c65c7fd54cc30e32f1fcb7661871971fed4d10c38cbc7fa219761c658ffd76d490e32c7fdb9aa9861967eed9d54c30cb1ff6e6aa5d8659fdb65552ec32cff9b02a1761963fe5d330bb0cb8ff2a1985d865e3fb30c3aec32d6febb6626619797ecc511330cb5bfaed9799865e5fd10cbccc32d6fdb961e6619797ecc30f330cbd3f65d8799865adfb7243ccc32e77db9aa9651977bcd8554b28cb5df6e6aa59465bef361552ca32df6db22a165196bbf5db30b28cb5df2e99859465cefd54cc2ca32f37ca8661651975bf55510b28cbcdf6628859465beeb6253aca32f37d9861d65196bbedc90eb28cb79f6d88759465af7d76d432832d7bdb66a1941979dedd510ca0cbcef6de8865065e7796f4432832f3bdb6a2194196bdedd510ca0cb9efaaa8865065e77b514432832d7bdb7a2194196bdedb510ca0cb5efaeda765065af7970d3b2832f3be8869d94196bdedb34eca0cb5efaed8765065af7b74c3b2832e7bcba61d941973df5530eca0cbcef6a18765065e77d10c3b2832f5bda761d94196bdedd10eca0cb9efaa88765065e77d1043b2832f5bd8721d94196bdedb10eca0cb5efaed8665065cf7d54c332832f3be8861994196bdf5daecca0cb9efaa97665065af7b70bb32832d7bcb85d9941979df442ecca0cbd6f61d7665065ed7b513332832f6be8899994197b5ed3cccca0cbdaf61e6665065ed790f3332832cf7ebb69897956ebedb1533bcab3dfaeda825a559efd76d392d2aed7cba9dc969576bed44ee4b4abf1f2da7725a55deed76d092d2aef75b8684969577ba5c3424b4abbdd6dda125a55dee96ed092d2adf76bb684969577bad43424b4abbdd69da125a55faeceed092d2acf7db7aa98695773edb554c34abbd76ceaa61a55bebb675530d2acf7db72a5869576bed394ec34ab3df6e89761a55dafd else 0x66cc8664075efd364433203af7f1b1219901d7b7cdc4ccc80ebdbe2e26664075edf511333203ad7f9b8999901d6bfc5c4ccc80ebcfea226664075edf30d333203af6f886999901d73fcdc3414cacb9fe2e1a0a6565cff36ed0532b2e7f8b7682995973fcd43414cacb9fe69da0a6565cfdd76d1130b2e7edb7688985973f65bb444c2cb9fb6d9a226165cfd96cd1130b2e7edb568898596bfcd85324c2cb8ffaa998261659fdd76d1130b2e7ee99688985973f6cc3444c2cbbdb6d5a226165e7db30d1130b2ef6da5688985969fedb953442cb8ff6a4a9a2165a7fb6f4cd10b2f37db5a66885979fcd8533442cb6fe6c299a2165a7f972d3d10b2d3fdb929e88596d7edb14f442cb6fd6c4a7a2165c7f952d3510b2d3fcb9696885971fe54b4b442cb6bf2d9a5a2165e6fd3252d10b2d3fdb8a6688596bfcd8533442cb6fb6c898a21658ff972d3d10b2db7db8296885963fedc554cbacb8ff2ea8865d65c7fd554432eb2c7fcbaa2197596bf6d9130cbacb5fe6c29925d658ffb744c12eb2e3fda826097596afedb9304bacb5fb6c89825d65e3fd10cb92eb2cff6bb684975973fb4cb424bacb9fd661a125d65cfe930d092eb2ebf6886849759777adb3424bacb1ffaeca961d65aff3614cb0eb2cfddb3aa9865969fedc532c32cb5fe6c29961965c7fd544c30cb2dbedb2261865969fe5cd10c32cb1ff6ea9921965aff3614c90cb2cdfebb69c865972fe5cb4e432cb97fa65a721965cbfb30d390cb2e9fe8869c8659767ed3b0c432cb3efaeda421965cf7d32d210cb2ebbe886908659775ec3348432cb9f7a65a321965cfbb30d190cb2ebde8868c865973eecbb46432cbbb7619a321965cfdd32d110cb2e7ed98688865975f744344432cb3fdaeda121965cfed32d090cb2ebf688684865973facbb42432cbbbd619a121965cff532d010cb2e7f998680865975fd44340432cb9fe65da021965ddf30cd010cb2e6feaaa6576597a7edbd32bb2cbd9f6d6995d965edf3614caecb2dcfdb7a6576596f7cd8532bb2cb73f6dc985d965bddb644c2ecb2f2fe99a2176597d3e5ad10bb2cbb9faa8a55d965ecfd3252aecb2de7db829576597d3f4414abb2cbf1f25ca55d965aff3614caecb2d7edb226176596f6ed990cbb2cb7bd6c4865d965bdf360432ecb2def9b0a6666596f3eda951332cb5bfaed9899965adf974cc4ccb2e6fcba66266596b7edb931332cbcbf6609899965bddb644c4ccb2f2fcb9a2266597d3e5ad11332cb5bf2e68899965e5fb31444ccb2cefcb969e6659757f4434f332cb79f6d4a799965bdf36053cccb2d6febb65e66596b7e5d32f332cb9bf2e99799965e5fd10cbcccb2f4fd9725e66596f7ad892f332cb5bf6e58799965adf972c3cccb2c7fcba66266596bf6d9131332cb1ff2e99799965e5f930c34ccb2e77cb72a58))) else (if i < 8 then (if i < 6 then 0x10cbaefb9a4680865d77ecd1b40432ebbfa689a021975dfe342d010cbad6fdb82a6665d737ed4953332eb5bf6e29999975adf972d44ccbad6fdb92a2665d797ecc131332ebcbf2a68899975e5fd33444ccbae6fca9696665d63fedc153332eb5bf6da99999758ff972d44ccbad6fdb6262665d71fe54d11332eb5bf2e58699975adfb72434ccbade7db521a665d6f6ed990d332eb7bd6c48699975bdf360434ccbae6fdb8aa9961d737e5c554cb0eb5bf6e2aa65875adf9715532c3ad6febb6a1961d737f55350cb0eb5bfaeca865875cdfd545432c3ae6fda82a1961d797ed4150cb0ebd9f6d4a865875edbb665432c3af6f5b12a1961d7b7cd8150cb0eb1ff6e2aa65875c7fb505432c3ad7ddb32a1961d6bfad8950cb0eb5fe6c0a8658758ffb735530c3acfddb3aa9861d63ff5db52c30eb5bfaed9661875cdfd54cb30c3af2fcb8659861d63ff5db52430eb9f76cda921875cff360d490c3ad6febb658861d737f5532c430ebcbf6e19621875adfb72c310c3ae6fda9618861d797ecc30c430eb3dfaeda521875cefb2cd290c3ae77da9694861d76bed3b4a430ebd9f659a5218759fbd76d190c3ae7ddb968c861d73eecb346430ebbb7619a321875cfbb52d190c3af6dd9668c861d77aed2b46430eb3feaeda021875cff372d010c3ae7f998680861d73fccb340430ebafe619a021875cff352d010c3af3f998680861d76fcd3b40430ebdbe659a021875def34ad010c3aefb9a4680861d77ecd1b40430ebbfa689a021875dfe342d010c3ad6fdb92a2661d797f5db31330ebcbf6e99899875e5f974cc4cc3ad6febb662661d6b7e5d331330ebcbf6a19899875e5f950cc4cc3ac7fdb92a2661d69ff5db31330eb8ff6e99899875c7f974cc4cc3af2fdb6662661d797e5b331330eb1ff2e99899875c7fb50cc4cc3ae3fca8662661d69fedcd11330eb9bf6a19699875cdf950cb4cc3af2fe8865a661d6b7edcb0d330ebcbf6618699875adfb72434cc3af2fd9821a661d6f3eda90d330eb7b76cc8699875bdeb62434cc3adef9b021a661d6bef5db4cc98eb5f72e1a664c75cfbb50d33263ad7debb619931d6beedd30cc98eb9f72e98664c75cfbd54c33263af6dda6619931d6bef5d90cc98eb5f76e88664c75cfbb74433263ae7deaa219931d7b6ec310cc98ebdd76d48664c75efb360433263af6ddba999931d7b6edc4ccc98ebdb72e26664c75edbb51333263ad7ddba999931d73ef554ccc98eb5f76e26664c75afb971333263af3de88999931d7b6ed34ccc98ebdb761a6664c75edb90d333263af3f9b6a21901d79fc5b510c80eb5fe6da8864075aff16d443203ad7fabb619901d79fd4430cc80eb5feaec8664075cff374433203af3fa88219901d7afcdb90cc80ebcfe6188664075edf30c433203af779b5219901d7bdcda10cc80ebdf else (if i < 7 then 0xcbec390eb2cabe9f6188659655f8faec3b2cb2af2fda869a9961ab7edb14b4cb0d9df694a5a6586afbb6652d32c357edb22969961b3eedb3474cb0d9f76d5a3a6586cfb96ad1d32c376ddb668e9961b3eed33474cb0ddb7699a3a6586cfbb4ad1d32c367dca568e9961b57ed434d4cb0dbb76d9a3a6586ddbb4cd1d32c34fddb3aa99561a7fcd8554cab0d5f76ce9965586afbb674c92ac3577db525c9561abbf5db2a4ab0d9bf6e6aa61886ddbb675530c4356fdb9aa98621af6ed9d54c310d1ff6e6aa618869fbb675530c43677db7aa99521b3bedb554ca90d5df6deaa65486cefd5453b2a43577ebb6199521abbe5d30cca90d9dfaa98665486afbb6653b2a4357edb229d9521abfcd814eca90d9df6e6aa65486bebb6653b2a435f6db229d9521afbcd814eca90dd5f2e99765486eafd54cbb2a4355febb65d9521b2ff5532eca90dd5f6d59765486eaf96acbb2a4376debb6199321bb6edab0cc990ddb72d58664c86afbd76c33264357debb6959321b3eed3b4ac990ddd7aed9564c86eebb6ecab2643775cb76559321abef5db2ac990d5feaeda764086aff370d3b204373fabb6199021b9fcdbb0cc810dcfe2dd8664086e7f36ac33204373f8b56199021abfd5db0cc810d5feaeda564086aff370d2b204367f9a76959021bafd5db2ec810dd7e6d59764086ebf16acbb204357fabb65d9021bbbd5db2ac810ddde6dd9564086eef16ecab204357fabb6559021a77f5db4a4c4cd6bf6d4a9a2266f5bb6654d11334efdb72a19599b57e5d510caccd3bfaeda825666d5fb504c12b335e7db52609599a77f5db4e4accdabfa21a725666bcfb6a4b92b336eedb86889599b7764c3444accdbbb6dda225666ddd92ed112b335bddb32a68899ad7eda94d444cd4ff2e5a5a2266b5fb6c52d11335bbdb42968899b3eed9953444cd3bf2e5a6a2266b5fb7053511334efdb5aa98699b76ed9d54c34cd7b76ceaa61a66d5fd554430d336e7da52958699a7eed9d54c34cdb9faeda521a66dcfb6ed290d336e7cb76948699a77f5db4a434cdabfa21a521a66ddeb6ed090d336ef5b56848699b1fe5d510caccd8ff6a09825666aefb6a4c12b33577db525c9599b57f4434c4accdabf6a186256669fdd76d112b3367ec986889599b5f7443444accd9fb25da225666dddb6cd112b336eed866889599a3ff5db504b2eb1ff6e89825975adfb6c4c12cbae6feaa658965d63fe5cd54c32eb3f76ceaa619758ffd7654b0cbac7fdbaa65865d63fe5cd54432eb3f76cca9219759ff3605490cbac7fdbaa64865d76bed3b4a432eb3f7aeda321975cfbb72d190cbae7de9968c865d776ec3346432eb9f76a5a321975debb4ad190cbacffabb680865d73fcdcb40432eb9fea65a021975dbf36ed010cbaebf986680865d73fcd4b40432ebb7e69da021975def34ad0 else 0x8665486d5fd54c332a4372fd976199521b97ecc34a4c4cdadf694a5a2266b5fd76c310cbaeafeaa618865d797edcb0c432ebcbf2e58621975e5fb52c310cbaf2fe99618865d7d3ec334a432ebeb7619a321975f5f30cd010cbaeafda82a2665d6d7f5db0c430ebabfaa98621875e5fb72c310c3af2fda9618861d7d3ec334a430ebeb7619a321875f5f30cd010c3aeafda82a2661d76bedb554ba8eb75f6daaa5d475baf970d32ea3add7ebb299751d76bf5514cba8eb75f6e0a65d475dafb4c532ea3add7ebb619751d6ebe5d30cba8ebb5faa9865d475bafd76432ea3aed7dba219751d6ebe5d10cba8ebb5faa8865d475eafb72432ea3afc7d86219751d7eaed990cba8ebf5e6c0865d475f8fb75332ea3afc7cba999751d7e3f554ccba8ebf1f6e2665d475f8f971332ea3afc7da8999751d7e3e544ccba8eb75f2ea665d475dafd55332ea3add7db8999751d6ebe5c4ccba8ebe5fa22665d475f8fb4d332ea3afc7ca6999751d7e3ec34ccba8ebf1f21a665d475d3fb4e53d10b2eafda629a88596d7f5db0c432cbcbfa658621965e5fb2ec310cb2fa7cb56188659797ecc30c432cbcbf660985d965dcfb5052aecb2ee7ca82957659797e4c30cbb2cbb9f25ca661565dcf94e5330ab2f37c9829985597d3ec310cc2acbcdf2617661565e6f9313330ab2e9fda729e881974fe5430ebb0cbb9f6e2aa59465dcfb6f552ca32de7db8aa965196f3edbd54b28cb79faeca859465dcfd54542ca32ee7da82a165196f3edb950b28cbe9f6ea8859465f4f975442ca32fa7eaaa2165197d3edbd10b28cbe9f2de8859465bcf975442ca32ee7eaaa2165197d3ed4510b28cbe9f2a28859465bcfb6f442ca32de7cb869d65197d3f4434eb28cbb9faa8a759465bcfb7053aca32fa7e8829d65196f3f5db0eb28cb79f2e98759465dcfd54c3aca32fa7e8861d6519773f5510eb28cbe9fa208759465d6fb50542ca32fa7db6a2165196f3edb510b28cbb5f69ca759465f2fb0e43aca32de7ebb6196519773f5530cb28cbe9f2a18659465f4fd10c32ca32de7ebb5d96519773f552ecb28cb79f6e17659465bcf970bb2ca32f67d985d965197d3f442ecb28cbf1f29d7659465f8fb0ebb2ca32fa7ebb61886957d3e5cb0c434abe9f6dd8621a55f4f96ec310d2afa7da761886957d3e4bb0c434abe9f618865da55f8fd76bb0ed2afc7cb95d876957e3edc2ec3b4abf1f2e1761da55f8f930bb0ed2afc7d865d876957cbec390f334ab6bfaed8621a55d5fd54c310d2af2fcb961886957c7ed3b0c434abe3f9dd8621a55f4fb6ac310d2afa7d8669486957d6ec3346434abebb619a221a55f5f30cd010d2adcfcb661d76956e7f5daec3b4abd3f2e5761da55e9f930bb0ed2afc7db55d87695757ed4151334abb3f69ca799a55f1fb0e43ccd2afa7d8621975957)) else (if i < 9 then 0x2d7fcba661761973fe5d330bb0cb9ffaa9985d865cffb50cc2ec32cffcbaa2176197afecc30ebb0cbcff661875d865ef7d76d432832f7bdb76a194197bde5bb50ca0cbdef6d9a865065ef7b514432832f7bcb7a2194197bdf5db4eca0cbdef6e1a765065ef7970d3b2832f7be8869d94197bdedb34eca0cbdefaed8765065ef7b74c3b2832f7bda861d94197bdf4430eca0cbdef69d8765065ef7b6cc3b2832f7bda821d94197bdf5db0cca0cbdef6a18665065ef7d10c332832f7bdb761994197bde5bb0cca0cbdef69d8665065ef7b0ec332832f7bc8761994197bdf5daecca0cbdef6e17665065ef7970bb32832f7bda85d994197bdf442ecca0cbdef69d7665065ef7b0ebb32832e7febb6a0969573fedbb504b4ab9ff2dda825a55aff9713b92d2ae7fda89dc969573fe5cd54c34ab3ff6deaa61a55dfbb675530d2ad7fcb9aa986956feed9d54c34ab5ffaeca961a55cffd5454b0d2ad7fdb72a5869573fe54b4ec34ab9ff2a4a761a55aff9733bb0d2ae7fca99dd869576ff5db4e434ab3ffaeda721a55cff972d390d2af5fcb969c86956bfe5ccee434ab5ff2e58621a55dbfb4ec310d2aef7e77694869577bec334a434abbdf69da521a55dfbb6ed190d2aefde7768c869577eec3346434abbf769da321a55dfdb6ed110d2aefed86688869577f6d3b44434abbfe6dda021a55dff4eed010d2aeff986680869577fcd3b40434ab3ff6e2aa5da55dfdb65552ed2adfedb2aa9769573ff55152bb4ab5ff6e0a95da559ffd76d42ed2ae7fcb96a1769573fe54b50bb4ab9ff2a4a85da55bff360542ed2ae7feaa26176956bfedb130bb4abd7f2a5875da559ff974c3aed2ae7fca961d76957b7f5512cbb4abdbf6a0965da55edf9504b2ed2af6fd87259769567fedd30cbb4ab5ff2e5865da55cff952c32ed2ae7fca921976956efedb90cbb4ab7df6d4865da55bf7b68432ed2adfddb321976956ff6d910cbb4ab7fd6c4865da55bff360432ed2acffebb6a0769573fe5cb503b4ab5ff6d8981da55aff972c30ed2aeff5b8684769577fac33423b4ab5ff6e0a999a55affb6e54ccd2af7f9b02a6669567fedb951334ab3ff6d8a899a55cff952544cd2ad7fdb726266956bfedb131334ab3ff2ea8899a55cff953444cd2ae7fc9869e669573fe5494f334ab7fe6c0a799a559ff974c3ccd2ad7fcb961e669573fe54b0f334abcff2618799a55cff95243ccd2adff9b021e66956bfe5ccef334ab9ff2a67799a55aff972c34cd2ae7fca961a66956bfe5caed334ab9ff2a57699a55b5f970d3532c36afdb5aa98621b57e5ad54c310d6bf6d6aa61886f5bb675530c435afebb6958621b57f5534ac310dabf69da561886d5fd5452b0c435afdb72958621bd3ed294ac310db9f694a561886dafb4e53b2a437a7eaa6199521bd3ed3b0cca90de9f29d else (if i < 10 then 0x3b42432cbbfd6d5a121965dff532d010cb2eff998680865977fccbb40432cbbfe25da021965dff30ed010cb2defebb2a576596f7edc152bb2cbdbf2a6995d965bdfb714caecb2f6fca966176596f7f5d930bb2cb7bf2e8985d965edf9524c2ecb2fcfdb726176597f3eda930bb2cbfbb6c8985d965bdf973442ecb2fe7cb5a2176596f7e5c34abb2cb9ffaaa995d965affb714caecb2f5fdb7a6576597bfcd8532bb2cb77f6de995d965bff3614caecb2d7febb661765973fe5d330bb2cb9ffaa9985d965cffb50cc2ecb2e7feaa26176596efedb930bb2cb7fb6c8985d965aff973442ecb2defdb6a2176596f7f5db0cbb2cbbdfaa8a55d965bff3614ccccb2cffdb72a266596bff5db31332cb9ff2e99899965affb6e4c4ccb2dfedb2262665967fe5d511332cb5ff2e68899965affd76cbcccb2e7fcba65e665973fe5432f332cb7fd6c497999659ff974c3cccb2d7fdb961e66596bfe5cb0f332cbbbf2a17699965fcf96abb4ccb2df7db825d85596fbedb94cc2acb7dfaed8661565befb6e4330ab2fe7ebb5d985597f3e5d2ecc2acbf9f2e57661565fcfb70bb30ab2fe7cb85d985597f3e4c2ecc2acb7dfaed7661565bef974bb30ab2f77ca95d985596fbedc2ecc2acbf5f61d7661565fcf94cbb30ab2fe7d865d985597f3e432ecc2acb7df2ea6661565f6fb0f3330ab2fe7d7699985596efedb90cc2acb7f76cc8661565bfdb644330ab2dff9b02198559777e5d2ecc2acbebf61d76615659ff974bb30ab2e7fda95d985597cfec3aecc2acb3ff2ea66615659ffb6c542eab2cffcbaa2175596bfe5cd10baacb9ff6a6885d565aff972c3aeab2cffcba619755973fed4b0cbaacb77f6dc865d565bf7b68432eab2dfddb321975596ff6d910cbaacb7fd6c4865d565bff360432eab2eefca85d9755967fe5d4ccbaacb9ff6deaa66065cff96f5533032e7fdb6aa998196bfedbd54cc0cb5ffaeda766065cffd54d3b3032e7feaa29d981973fed314ecc0cb9ffaeda666065cffb6ed333032e7fcb769998196ffad894f440cb5ffaeca865c65eff3605432e32d7fcbaa21971973fe5d510cb8cb9ffaaa8865c65ebf96f4432e32d7fdb6a21971973fedcd54c38cb3ff6daaa61c65df7b695530e32dfbdb4aa9871979ff5db30c38cbcffaa99861c65affd76cc30e32e7feaa661871973fed4d10c38cbcff6628861c65ebfd10cbb0e32f3fd98699871973ff5db52438cb3ffaeda621c65cffb30d310e32e7fdb9aa9861967fedbd54c30cbbf76ceaa61865bfbb675530c32d7febb661861973ff55330c30cb5ffaed9761865aff974cbb0c32e7feaa65d86196bfedcb0ec30cbcff6618761865ebfb2ec3b0c32d7fdb921d861973fedcd54bb0cb3ff6e2aa5d865dfdb65552ec32dfedb2aa9761967ff5db50bb0cb7fe6c0a85d865affd76cc2ec3 else 0x565eff170d0532b2f7f9b768299597bfc5bb414cacbbfe6e1a0a6565dff170d0532b2eff9b7682995977fc5bb414cacb5ff6e29926165affb6f4c930b2cffebb69c985973ff4cb4e4c2cb9ff661a7261659ffb6cd3930b2ef7da7694985977bed334a4c2cbbfbaeda226165dfdb6ed1130b2efecb7688985977f6db3444c2cbbfb2d9a226165efdd32d1130b2efeda7688985977f6d33444c2cbfdb6d5a226165cffd7654d10b2e7fdb72a6885973fe5b953442cb9ff6d8a9a2165cffb6a54d10b2cffdb72a688596bfedb953442cb9ff6ea99a2165affb714cd10b2d7fdb7a6688597bfcd8533442cb9ff2a699a2165bff3614cd10b2cffcba662885967fe5cb4f442cb9ffa65a7a2165affb7253d10b2e7fca929e88596f7edb14f442cb7fd6c4a7a2165cffd32d3510b2e7fca929a885977be5494b442cbbdf29ca5a2165def94c52d10b2d7febb2a197596bfe5d510cbacb9ff2ea8865d65cffd554432eb2d7fdb6a2197596bff5d930cbacbdfb6c89865d65aff9734432eb2d7fdb8a64975967ff5db504bacb9ffa65a825d659ffb6cd412eb2d7febb260975973fed41304bacbddf6d49825d65efdb644c12eb2cffdba26097596ff6d91304bacb5ff2e68825d65dfeb70d092eb2eff498684975977fb443424bacbbfd6d9a125d65cffd7654b0eb2e7fdb62a5875973feda952c3acb5ffaeca961d65cffb754cb0eb2d7fcbaa65875973ff55532c3acb5ff6e29961d65eff3614cb0eb2cffdbaa65875973fe54d32c3acb7fe6c29961d65cff952d330eb2e7fca929987596ffad894cc3acb5ff2e5a561d65cff952d2b0eb2cffdb7aa9865977bedad54c32cbbf76ceaa61965befb6b5530cb2dfddb3aa9865973ff55532c32cb5ff6e29961965e7fb714cb0cb2d7fdb7a6586597bfcd8532c32cb6ff6e29961965bff3614cb0cb2e7feaa661865979ff4c930c32cb7fb6c89861965aff9734430cb2e7fca929d86596bff5db2ec32cb9ff2e99761965cffd54cbb0cb2dff5b125d86596bfedcb0ec32cb5ff2e58761965defd5452b0cb2e7fdbaa6486596bfedc532432cb5ff6de9921965eff3614c90cb2dff9b0a6486596bff5db30432cbb7faeda721965dbf972d390cb2edfe9969c865976fecc34e432cbb7f6d5a7219659ffd76d390cb2e7fe9969c865973fecc34e432cb5ffaed9721965dbfb4ecb90cb2cffdba25c865976fed392e432cb7fd6c49721965affb72c390cb2d7fcb961c865977df4cb48432cbbef661a421965df7b6ed210cb2efbd97690865977de4bb48432cbbef6d5a421965dfbd32d190cb2efdd9868c865977eecbb46432cbbf725da321965dfbb0ed190cb2efee99688865977f6cc344432cbbfb65da221965dfd92ed110cb2eff699684865977facc342432cbbfd6dda121965dfeb2ed090cb2eff497684865977fac)))) else (if i < 17 then (if i < 14 then (if i < 12 then 0xeaa2a5865d6bfedd532c32eb9ff6ea9961975aff9754cb0cbae7feaaa65865d6bfedb532c32eb3ff6ea9961975cff9534cb0cbacffcba659865d73fe54b2cc32eb9ff2a49661975cff952d2b0cbacffcb9aa8865d6bff5db52432eb5ff6ea9921975cffb754c90cbae7feaaa64865d6bfedb532432eb9ff2a69921975aff972c310cbae7fda9618865d77bec334a432ebddfa65a521975dbfb4ed290cbaefddb968c865d77ef4cb46432ebbf7659a321975dfbb0cd190cbaefddb568c865d77eed4b46432ebdf7a65a321975dfbb4ad190cbaeff9b9680865d77fd4cb40432ebbfe661a021975dff36ed010cbaeff996680865d77fcc3340432ebbfe6d5a021975dff352d010cbaf7fa99680865d77fcd3b40432ebbfe695a021975cffd7654cccbae7fdb82a6665d73fe5c153332eb9ff6d4a9999759ffb7054cccbad7fdb82a6665d73fedd533332eb5ff6e29999975affb6d4ccccbae7fca9a66665d67fe5cb51332eb9ffa65a899975cffd32544ccbacffdb62a2665d6bfedc951332eb9ff2a4a899975cff952cc4ccbad7fdb6262665d73fe54931332eb3ff2ea8899975cff953444ccbacffcba65a665d6bfe5cb0d332eb9ff2a58699975edfb715532c3af6fcb8aa9961d7b7f5db50cb0ebdbfaa9a865875edfd545432c3af6fda82a1961d73fedc554cb0eb9ff2e2aa65875affb715532c3ad7fcb8aa9961d6bff5db50cb0eb9ffaa9a865875affd765432c3ae7feaa2a1961d73fed4150cb0ebddf6d4a865875efbb665432c3af7f5b12a1961d7bfcd8150cb0eb9ff6e6aa61875dfbb675530c3adfddb3aa9861d73ff5db52c30eb5ffaeda961875cffd54d4b0c3af6febb659861d7b7f5532cc30ebdbf2e19661875affd76cb30c3ae7feaa659861d73ff5db52430eb5ffaeda921875efbb66d490c3af7f9b06a4861d7b7f5db2c430ebdbf6e19621875affd76cb10c3ad7fdb9618861d73fed4b0c430ebdbf6598621875defb0cd290c3aefdd8668c861d77fcc3340430eb3ff6d8a899875e7fd76cc4cc3af3fcba662661d79fedb331330eb5ffaed9899875cffb74cc4cc3ad7fcba662661d73fe5d331330eb9ff6a19899875e7f950cc4cc3acffcbaa22661d7b7edc32d330ebdbf2e19699875edf950cb4cc3af6fe8865a661d73fe5432d330eb5ff6e58699875e7fb30c34cc3af6fd9661a661d7bef5db4cc98ebdf76e1a664c75efb970d33263af7debb619931d7beedd30cc98ebdf76998664c75efbb74433263af7dda6219931d7beec310cc98ebdf72e26664c75efbb51333263af7de88999931d7beed34ccc98ebdf761a6664c75eff16d443203af7fabb619901d7bfd4430cc80ebdfe6188664075eff171333203af7fa88999901d7bfcc34ccc80eb9ff6dda8a6565cff96ed4532b2d7fcb869e995973fed434f4cacbdfe6e1a0a6 else (if i < 13 then 0x4ad04680435040203d803a50372033f030c02d902a602730240020d01da01a701740141010e00db009f00630030002a0024001e00180012000c00060000cffb4ed2d32c367fda66969961abfedb94b4cb0d9ff69ca5a6586cff94e52d32c357fdb62969961b3fed314b4cb0dddf694a5a6586efbb6cd1d32c377dda668e9961bbeedab474cb0ddf72d5a3a6586efbb4ad1d32c377dca568e9961bd7ed434d4cb0dbbf699a5a6586ddfb4c52d32c36fddb668e9961b7eedab474cb0dbf72d5a3a6586fdbb6cd1d32c36fdda668e9961bf6ed33474cb0dbf7695a3a6586dfb94ad1d32c34ffdb7aa99561b77edb554cab0dbf76ceaa65586dff3615532ac357fdb7a659561bbbedad32cab0ddf76ce9965586befb6b4cb2ac35fddb3a659561b3ff5532ecab0d5ff6de9925586efbb674c92ac35fddb3a649561a7ff5db4e4ab0d9ffa65a725586affd76cb92ac34ffdba25c9561bbbf4cb2a4ab0d9ff6e6aa618869ffb6b5530c436fddb3aa98621afeed9d54c310dddfaed8665486eef974c332a43777eaa6199521bbbedbb0cca90dddf2dd8665486eefb4ec332a43777ca76199521abff5db0cca90d9ff2e98665486cffd54c332a43777db56199521bbbe5ab0cca90dddf6e6aa65486befb6f5532a435f7ebb69d9521a7fedbd54ca90dd7faed9765486ebf974cbb2a4375feaa65d9521b3ff5532eca90dddf6d59765486eef96acbb2a4377debb6199321bbeedab0cc990ddf72d58664c86efbd76d2b264377ddb76959321bbee5bb4ac990ddf7aed9564c86efbb6ecab264377dcb76559321bbfd5db4ec810ddfe6e1a764086eff36ad3b204377f8b569d9021bbfd5db0cc810ddfe6dd8664086eff16ec33204377f9b56199021bbfc5ab0cc810ddfeaeda564086eff370d2b204377f9b76959021bbfc5bb4ac810ddfeaed9764086eff36acbb204377f8b565d9021bbfd5db2ac810ddfe6dd9564086eff16ecab20434ffebb6949899b3feda953444cd9ff2d4a9a22669ffb6b5530d336fddb3aa98699afeed9d54c34cd9ff2ea8865666affb6f4432b334ffebb6a09599abff5d9304accd9ff6a09825666affb6e4c12b33777db52609599a7ff5db4e4accd9ff261a725666cffb504b92b336fedb86889599b7f7443444accdbfb6dda225666cffb70d3532bae7fcb869a995d6bfe5c34d4caeb9ff6a1a6a6575cffd76d412cbae7fdb56a0965d6bfedc5324b2eb5ff6da99259759ffd76d412cbae7fe996a0965d73ff553304b2eb9ffaa89825975affb6c4c12cbacffdba260965d6bfe5c32c4b2eb9ff6a19625975cffb735530cbacffcb9aa9865d73fe5cd54c32ebbf76ceaa61975affb735530cbadfddb3aa9865d6bff5db52c32eb9ffaa9a961975cffd7654b0cbae7fdb62a5865d73feda952c32eb3ffaeca961975affd7654b0cbae7f else 0x3d413d3b3d2c3d263d203d113d023cf33ce43cde3ccf3cc93cba3cab3ca53c573c1b3c0c3bf43be53bd63b883b793b6a3b253ad73a893a3b3a2c39e7399039543918390938cd38b5388b384638373828382237dd378f3777375f371136f936bd367836603612360335f435e535cd35be35af35a9359a358b3585357f35673558354935313522351334fb34ec34dd34ce34bf34b934aa34923483347d3453344d3447342f34203411340233f333e433d533c633ae337b337533663360335a334233333324330c32fd32f732e832d932c132b232a33294327c326d326732583249323a3222320a31fb31f531e631ce31ad3195318f3189317a316b316531563147312f310530f630de30c630ae3096307e3066305730483039302a3024301530062ff72fdf2fd92fd32fc42fbe2fb82fa92fa32f9d2f8e2f5b2f552f462f402f3a2f342f252f1f2f192f0a2efb2ef52eef2ee92ee32edd2ed72ec82eb92eb32ead2e9e2e8f2e772e5f2e502e4a2e3b2e352e2f2e202e1a2e0b2dfc2ded2dde2dcf2dc92dba2db42dae2da82da22d9c2d962d902d8a2d7b2d752d5d2d4e2d3f2d392d212d1b2cfa2ceb2cdc2ccd2cc72cc12cbb2cac2c5e2c072bf82bb32b772b322aff2aba2a752a272a182a0929a9299a298b293d292e291f290728f828b32865285628472841283227ed279f275a270c26fd26ee26df26d0268b263d25f825aa255c251724d224962448240c23be23af236a231322ce2289227a223522262217220821f921ea21db21cc21c621b721b121ab219c218d217e217821692163215d2157214821422133212420cd20912082203d202e201f201020011ff21fe31fd41fc51fb61fa71f981f801f7a1f6b1f531f3b1f351f261f171f111f021eea1edb1ecc1ebd1eae1ea81ea21e9c1e961e871e781e691e5a1e4b1e3c1e361e301e2a1e1b1e031df41de51dcd1db51daf1da91d881d821d731d6d1d5e1d461d371d281d101cf81ce01cc81cb01c981c801c7a1c6b1c5c1c561c471c381c201bff1bf91be11bdb1bc31bab1ba51b9f1b991b931b8d1b871b811b7b1b751b6f1b691b631b5d1b571b511b4b1b451b3f1b391b331b2d1b271b211b1b1b151b0f1b091b031afd1af71af11aeb1ae51adf1ad91ad31acd1ac71ac11abb1ab51aaf1aa91aa31a9d1a971a911a8b1a851a7f1a791a731a6d1a2819d11983192c18e718ab186f183317f717bb177f1755172216ef16aa16771644161115d515a2156f152114d31485142e13d71389133212ed12a8125a11fa11a31167112b10dd1086102f0fe10f930f450ef70ebb0e7f0e430e100ddd0d980d650d320ced0ca80c750c0c0bd90ba60b730b490b160ad10a8c0a500a1409d809a50960092408fa08be08820846081307e007a40768073506f906c6069c0669062d05f105be05820546051304e0)) else (if i < 15 then 0x910b910590a590729063904b8feb8fdc8f858f408f288eda8e8c8e3e8e2f8df38db78d7b8d368cdf8cd08c798c348be68bce8bad8b958b508b028ab48a5d8a1889d3897c892e88f288da88b988b388928883883e87f087b4876f871886d3868e863785e085a4855f850884f984f384ed84d584cf84c084a884908481847b846384548445843684278418840983fa83f483e583a9839a838283738364834c833d833782e082d182c282aa829b8295828682778268823581f081b481a5818d817e8130812180dc80cd80b580557ffe7ff87ff27fad7f717f1a7ed57e907e4b7e0f7db87d6a7d5b7d1f7cd17cc27c7d7c387c297bed7b9f7b5a7b547b187ad37a8e7a5b7a1f79e379b079a1799b798c797d795c79567950794a793b78ed78de7899788a787b786c785d7845783678277818780977fa77ac775e771076f876aa769b7695768f764a760575c0757b752d751e74d074947458740173ce738973717311730272ab726f7233722471d671d071ca71bb71ac719d714f710a70bc7077705f70116fc36fb46f786f336eee6ed66e916e436df56def6db36d6e6d296ce46c9f6c636c1e6bd96b9d6b856b766b676b586b496b316b196b016ab36aa46a566a0869f069e16993694568ee68df689168436834681c67fb67da67cb67b3679b6783676b672666e166a5664e661265d665c765946546650a64c564ad64a7646b642f64206411640263f363a563966351630c62fd62ee62d662c762b862a96264621f61d161b9616b6126611760db60d560cf608a604e60125fd65f9a5f8b5f7c5f6d5f285ee35ed45ebc5ead5e5f5e1a5dcc5d905d395ceb5c9d5c4f5c0a5bbc5b6e5b0e5ab75ab15aa25a665a2159e559df59a3598b5985597659675958594059315922590a58fb58ec58dd58ce58bf58b958aa585c584d57ff57e75799578a577b571b56d656915643563d562e55e955e355d4558f554a54f354e454b1545a541553d0538b533d532e531f531952b9527d5265521751c0517b5163514b513350e550cd50ac5067502b50134fd74fb64f714f354f1d4f054eb74e9f4e634e424dfd4dc14da94d6d4d4c4d3d4d2e4d1f4d074ce64cb34c774c3b4c2c4c1d4c174c114c0b4c054bf64bba4b754b304aeb4aa64a8e4a764a674a584a494a3a4a344a254a1f4a194a0a49e949e349dd49c549ad499e498f49804968496249534917490848b14863480c480647b8476a474047164710470a470446c84683463e45f945b445a5459645874578453c452d451e4518450944c444b544a6448e44884479446a445b444c443d440143f243c843b9436b434a433b432c430b430542c04269425a424b423c41e541a0419141824173411c40c54089407a4062405c4044402c3fd53f7e3f4b3ef43eb83e733e253e163dd13dc23dbc3dad3da73d8f3d773d5f3d50 else (if i < 16 then 0xa08fa089a083a07da077a071a06ba065a05fa059a053a04da047a041a03ba035a02fa029a023a01da017a011a00ba0059fff9ff99ff39fed9fe79fe19fdb9fd59fcf9fc99fc39fbd9fb79fb19fab9fa59f9f9f999f939f8d9f879f819f7b9f759f6f9f699f639f5d9f579f519f4b9f459f3f9f399f339f2d9f279f219f1b9f159f0f9f099f039efd9ef79ef19eeb9ee59edf9ed99ed39ecd9ec79ec19ebb9eb59eaf9ea99ea39e9d9e979e919e8b9e859e7f9e799e739e6d9e679e619e5b9e559e4f9e499e439e3d9e379e319e2b9e259e1f9e199e139e0d9e079e019dfb9df59def9de99de39ddd9dd79dd19dcb9dc59dbf9db99db39dad9da79da19d9b9d959d8f9d899d839d7d9d779d719d6b9d659d5f9d599d539d4d9d479d419d3b9d359d2f9d299d239d1d9d179d119d0b9d059cff9cf99cf39ced9ce79ce19cdb9cd59ccf9cc99cc39cbd9cb79cb19cab9ca59c9f9c999c939c8d9c879c819c7b9c759c6f9c699c639c5d9c579c519c4b9c459c3f9c399c339c2d9c279c219c1b9c159c0f9c099c039bfd9bf79bf19beb9be59bdf9bd99bd39bcd9bc79bc19bbb9bb59baf9ba99ba39b9d9b979b919b8b9b859b7f9b799b739b6d9b679b619b5b9b559b4f9b499b439b3d9b379b319b2b9b259b1f9b199b139b0d9b079b019afb9af59aef9ae99ae39add9ad79ad19acb9ac59abf9ab99ab39aad9aa79aa19a9b9a959a8f9a899a839a7d9a779a719a6b9a659a5f9a599a539a4d9a479a419a3b9a359a2f9a299a239a1d9a179a119a0b9a0599ff99f999f399ed99e799e199db99d599cf99c999c399bd99b799b199ab99a5999f99999993998d99879981997b9975996f99699963995d99579951994b9945993f99399933992d99279921991b9915990f9909990398fd98f798f198eb98e598df98d998d398cd98c798c198bb98b598af98a998a3989d98979891988b9885987f98799873986d98679861985b9855984f98499843983d98379831982b9825981f98199813980d9807980197fb97f597ef97e997e397dd97d797d197cb97c597bf97b997b397ad97a797a1979b9795978f97899783977d97779771976b9765975f97599753974d97479741973b9735972f97299723971d97179711970b970596ff96f996f396ed96e796e196db96d596cf96c996c396bd96b796b196ab96a5969f96999693968d96879681967b9675966f96699663965d96579651964b9645963f96399633962d96279621961b9615960f9609960395fd95f795f195eb95e595df95d995d395cd95c795c195bb95b595af95a995a3959d95979591958b9585957f95799573956d95679561955b9555954f95499543953d95379531952b9525951694fe94e694aa946e942093db93a89399934b933c92e592b2927f9255922291e691aa916e913b9135912f9120911a else 0xf82514793c7e2f0ca2813f93c7e2f0f82793793c7e2f04a49f278fc5e197c9e3f1786433793c7e2f0ca66f278fc5e197c9e3f1787c0292bc9e3f17825f278fc5e1f04a27f1f8bc3e097c9e2f0f80692f93c7e1f00ce513f93c7e2f04be4f1f8bc23294cde4f1f8bc12c1fc9e3f1782583f93c7e2f04a49f278fc5e19491e4f1f8bc32c9fc9e3f1784933617c9e3f1785c130a3c9e3f0f825000000000000aab5aaafaaa9aaa3aa9daa97aa91aa8baa85aa7faa79aa73aa6daa67aa61aa5baa55aa4faa49aa43aa3daa37aa31aa2baa25aa1faa19aa13aa0daa07aa01a9fba9f5a9efa9e9a9e3a9dda9d7a9d1a9cba9c5a9bfa9b9a9b3a9ada9a7a9a1a99ba995a98fa989a983a97da977a971a96ba965a95fa959a953a94da947a941a93ba935a92fa929a923a91da917a911a90ba905a8ffa8f9a8f3a8eda8e7a8e1a8dba8d5a8cfa8c9a8c3a8bda8b7a8b1a8aba8a5a89fa899a893a88da887a881a87ba875a86fa869a863a85da857a851a84ba845a83fa839a833a82da827a821a81ba815a80fa809a803a7fda7f7a7f1a7eba7e5a7dfa7d9a7d3a7cda7c7a7c1a7bba7b5a7afa7a9a7a3a79da797a791a78ba785a77fa779a773a76da767a761a75ba755a74fa749a743a73da737a731a72ba725a71fa719a713a70da707a701a6fba6f5a6efa6e9a6e3a6dda6d7a6d1a6cba6c5a6bfa6b9a6b3a6ada6a7a6a1a69ba695a68fa689a683a67da677a671a66ba665a65fa659a653a64da647a641a63ba635a62fa629a623a61da617a611a60ba605a5ffa5f9a5f3a5eda5e7a5e1a5dba5d5a5cfa5c9a5c3a5bda5b7a5b1a5aba5a5a59fa599a593a58da587a581a57ba575a56fa569a563a55da557a551a54ba545a53fa539a533a52da527a521a51ba515a50fa509a503a4fda4f7a4f1a4eba4e5a4dfa4d9a4d3a4cda4c7a4c1a4bba4b5a4afa4a9a4a3a49da497a491a48ba485a47fa479a473a46da467a461a45ba455a44fa449a443a43da437a431a42ba425a41fa419a413a40da407a401a3fba3f5a3efa3e9a3e3a3dda3d7a3d1a3cba3c5a3bfa3b9a3b3a3ada3a7a3a1a39ba395a38fa389a383a37da377a371a36ba365a35fa359a353a34da347a341a33ba335a32fa329a323a31da317a311a30ba305a2ffa2f9a2f3a2eda2e7a2e1a2dba2d5a2cfa2c9a2c3a2bda2b7a2b1a2aba2a5a29fa299a293a28da287a281a27ba275a26fa269a263a25da257a251a24ba245a23fa239a233a22da227a221a21ba215a20fa209a203a1fda1f7a1f1a1eba1e5a1dfa1d9a1d3a1cda1c7a1c1a1bba1b5a1afa1a9a1a3a19da197a191a18ba185a17fa179a173a16da167a161a15ba155a14fa149a143a13da137a131a12ba125a11fa119a113a10da107a101a0fba0f5a0efa0e9a0e3a0dda0d7a0d1a0cba0c5a0bfa0b9a0b3a0ada0a7a0a1a09ba095))) else (if i < 20 then (if i < 18 then 0x781c59fc7e1f078bc945981187c371387c2e0f168f09228be4f1f8a60401f89c3e170781c5a1c00f8fc3e083d17c9e21c1007a2f93c7e2f0f814d4f93c7e2f09228be09c9145f278fc5e1d34ee0058be4f1f8a4de0644fc007c00f8017003e084c20e80183c008003801d003a004050030400314102c20d8410701c0de4f1f8bc3e0a2d3e4f1f8bc34593cda0074c48a2f93c7e2f0cec5858b0e801d003a007400e801d003a005400e80142914203400d1642151642101c00780081c0040bc00b810f001600385040000010a0f001e003c007800f80102003800c8a4017801e04205e004356004040a350a8038340081c00544a00b800e161e06802e06802e06822e06802e06802602822930142011a0c98103810c141e0680251a85401c105d00402894014174010000000000000000000000000000000000000000000000000000000000000000000000000000000087f278fc5e1f02227c461cef0d33793c5e1f05388c3c37c9e3f0f80d746230e758699bc9e3f17869f278fc5e1f04220f3c1fc9e2f0f82333793c5e1f0422293423c5e4f1f86253423c9e3f1786253793c7e2f0c22253197c9e3f1787c13793c5e1f04925f278fc3e0964be4f1f87c128525147f278bc3e09fc863f1787c12f93c7e2f0f825f278fc5e1f04a28f278bc3e08a4de4f1f8bc03897c9e3f1786252b8cf386c2f93c5e1f050e13c61b0be4f1f8bc141a1c186c2f93c7e2f0d10d94117c9e3f1787c0c6a46928b1b198be4f1787c14d8264c662f93c7e2f0d032945818cc5f278fc5e1a68d45f278fc5e1f00ec6f278fc5e1f031473419f0d85f278bc3e0a0d06726a410b86f278bc3e0ab20e0341cb0d85f278bc34e1b0be4f1787c1361b0be4f1787c131a0cf86f278fc5e144d04e3419d0de4f1f8bc389a4d06726e1bc9e3f178513499dc87ac378fc5e1c4d068719d30de4f17871341a1c473c3793c7e1c4d067709e30de4f1f8b13461bc9e3f178712338c1be4f1787c133801be4f1f8bc33423c9e3f0f825f278fc5e1704ae00683bc9e3f17867c3f83c9e1f1cbe4f1f87c04894dd8df1f93c5e1f04e85f278fc5e1f021e7c2f8fc5e1f04a75d23832268c399b0be3f1786bc2f8fc5e1f04b85f1f8bc3e09615e4f1f8bc12f93c7e2f049e431f8bc3e09451e4f1f8bc3e013ce2813f93c7e2f0f82714793c5e1f00d2614793c7e1f00ce614793c7e2f08ca6f278fc5e1f04a28f278fc5e1f009e7f278bc3e01c8d26f278bc3e0938be4f1787c0399bc9e2f0f8050349bc9e2f0f8050349bc9e3f0f80672f83c9e119f8e514793c7e1f00ce6f278fc3e0140ce6f1f87c03a19ca34f2787c02819cde4f1f8bc23297c9e3f17864f1793c3e3194a28f278fc5e1194c28f278fc5e1194de3f178474329469e4f17845032986628f278fc2329bc9e3f10e0652f93c662f0 else (if i < 19 then 0xfc5e0f278670682078511e108083826606c10e14102c3e4f1787c185c6cc0d050681b02004428208c3e1749a3f0f821b420ac0800e0a0834141581001818733793c7e2f0a2670701b0be4f1f8bc3e083d3e007c10c9810701c0de4f1f8bc3e0c2d387f278fc5e144c387f0036007c1081c0c0ef278bc1e3f0e149038181de4f1f8bc3e062d20ef1f8bc3e0e2cce0060ce008042580282b8020401c0de4f1f8bc3e0a2d20e03317c9e3f1787c08727c9e2f0f830f28200e06f278fc5e1f0316907793c7e1f07166870a3c9e3f17878b381c0de4f1f8bc3e0a2d00787c3e062f8d0fe4f14fa0040d00201134016808c1680901682142c307801020838305060e0c161810e0800784cd0803a0399bc7e2f0f8223419b0be2f0f83c732441717822f04287040e6631984c1e2489a08700360040e63309802262340e6602890c66230980d040b0d007f1f8bc3e088d1a4f1f87c011f10b0d144441061a3c7e1f0617c53844d00733617c7e2f0f82903e17c7e2f0f826c3f83c7e2f0a466704266d278bc7e148cd117005e3f0f89232044d1e0f1f8bc22c9dc10b82103c185d278fc5e143ce6612617c7e2f0f820f458e0e158dc011a04985f1f8bc3e083d162838585f0f8349e3f14d85f1f8bc3e0839a27b141c248f87c185d278e0fe2a1220d801488291b0456087c1081e007c00c000990a17801f043e030c5e087c10e144216141f0038507800c1c08447c08bc00c0241188bc0240068c4e17801e002c50780089a1628345040be00948a351285412c02686082c7e008690b16131f802e04300cc16282e3f005c084640b14171d802a003070015303c08445c08849e00b810c1e20445e00b45e01387a27005001c0044c081e007c00e884e10904622e008278744270b44270b44278944278b44270b44c00b800f801f042e0860138236058b0b8c4e1000514180032030014505c8e371385c12c0c5840000b24204064068a0c00000000314162c3040c585c0089380108c4e118c101c0080070218248098816002620780080c0040000020020804e08027b18563068b08066a2c40190c6620c4f0d88113c2040078010449bc9e3f1787c145a01c06c2f93c7e2f0f820e4d80173217c9e3f1782c33b9bc5e0f278f0b33981be4f1f8bc1619fc1e4f1f8b0b2e17c9e3f1187c0e69c0e857238dc4e0734f88c3f1b89c2e0f038b4580170020e0401c8cc5f278fc5e1f015c005c0082389c3e17078007a2d0e085c108238b170210471385c1e00538b38238dc4e1707801462d0e005c0081c00411c4e1f078013e2ce08e371387c1e004d8a471b87c1e006827c59c2808e371383c009f168300260040f0d0010471387c2e084b8b38238dc4e1f0b821262d1c6e1f0b821a0971670a0238dc4e170425c5a02608e371387c1097148e371387c20c04b8b3e1f0dc4e1f else 0x78bc3e033ce107045061bc9e2f0f80cf361b0be4f1784cf32401f043e0852009a00c6230243c9e13390e0040c6431184c010338f86c2f93c3e2f01a277003600521600ac10e821d042063218cc461049a07c378b13e4f1f84cf39a0cf86f278fc5e1c4d16350046803190c66230824cf461b0be4f1f8bc2679d410f93c7e2f0e24cf34102270de4f1f8bc2679f0de3f178712679b0de4f178712679b0de4f1f8712679b0de4f1f8b12679b410e8219002063218cc4610499c7c3793c3e3f1624d13a80171c80290430d7331fc5e4f1f878b4035cde4f1f8bc2609d8f6062f861be4f1f8a806f93c7e2f0b9a663b998be4f1f8bc36006d2e662f93c7e2f0d801b431dcc8df278fc3e027d08d63b1611e3f0f83c94237c9e1f1f82c4e69e10e662f93c3e3b1782809a37c7e1f0790c4c7a026c773315c862f1f87c08dab0fa6c2a83c9e3f17841b4c1e0058be4f1f87c08d99cce43138fc3e0468e13f1d8bc3e046cc0793c762f0f811b310bc0141a0058a0a821501022f003e007c0450bc0091c1f00245048a081a0041b87d3617c9e3f17868f0020e03793c5e0f1f845147808e101fc9e3f1787c00e06d1e006c108380e0602f93c7e2f0f801b502349a3d0a8bc10d1fc9e3f17841b85d34e0753017c9e3f1787c144185861be4f1f87c185d34f0780193317c9e3f17811b3819c8e271987c08d9c2c8d63c998be4f1f8bc14f8019378fc5e0254a08038180be4f1f8bc3e0a70f8526f8fc5e1f24f87e3623c9e2f0f8270681fc9e2f0f83c638370fa6c2f93c5e1f1d10787c10c00e068180be4f1f8bc3e043d5e4f1f8bc20dc3cdc083840762f93c7e2f0f808d40381046f278fc5e1f041e90711bc9e2f1f87c13f020e10228b17020e10218c44f1f8bc3e083d1c0838408e031430431bc9e2f0f82293b1bc9e28a787c137020e1023c963f0f8bc1302380c58c10c6f278fc3e089cec6f258bc7e1f04dc07005c083840863107c9e3f17820f47020e1023c9e3b0f8bc1302380c58c10c6f278fc5e1894ec6f278bc7e1b04d40838408f278fc312f14c08a031634283e007c10e15c010185c4d0fc7e1f16149b2f93c785f17805d3791c5e1c2f8fc136141f00300100145041b85f0f93c7e29a1b85f0923c9e3f04fe4f08530d85f17827f23870de3c2f8bc13e1bc9e1f1e1425e29d40400891e00b410f8010683a0040f002001a00586c1600700046f004497005a087c008341a1500203c00910864220e808036821070340de4f1787c7e04393a6d268f43a0478230f4034100602f93c7e1f17829801be4f1f8bc3e042b9a803f93c7e2f0f820b66a0cde1f043641b19bc10d9008007278bc647f0786604793c5e323f87c13823c9e27191fc3e09c11e47178c8fe1f04e08f278bc647f0b8277043e187c50b821f2787c705f1782670430586003c26ec6f8)) else (if i < 21 then 0x24f0040780103f80212f802f0020097c110bc143822f050f0f8013003e0040f00328a3f93c5e1f04de0840e630b800f00111f00243c204a38dc5e230f85c1e061c9e003c0840fc08b800803804700f801f17860fe3f04b07f278bc7e1f0294783f93c6a5f17826900225f004e0041ee643c97c9e1f1f82870028792f93c3e3f039a7f002e3f0040e068180be4f1f8bc3e0839408038180be4f1f8bc3e0a40800c05f278fc5e1f04f88c3f93c5e1f04c08038180be4f1f8bc3e0240c05f278bc3e0f1ce28f1f93c5e1f009e71409dc7e4f1787c138a3c7e4f17846530200be4f1f8bc3e00689e9228a3c7e4f1787c027a1c108e469e4f1787c130218cc50a793c5e1f05008845027b1f93c5e1f04ec614793c5e1f00d2730420819793c7e2f0cc086331425e4f1f8bc34317c7e1b0793c4329e01478fc9e2f08ca6628a3c7e4f1784653b1851e3f278bc2329fc7e2f08e86528d051e4f17846530a3c633f278465378fc9e21c0ca5f00306801f0024420f803800808a08381be4f1f8bc3e003d1a00411e4f1f87c5e013cfa006c00e801d043a02305a087410a821f043e084d186c2f93c7e2f0f828c3617c9e1f1f8bc068a0d186c2f93c7e2f0f828b1b80203014c86331184c068a1c10c1061bc9e3f1787c0689f0d85f278bc3e0344f86c2f93c7e2f01a27c3617c9e3f1784d1381f0de4f1f8bc3e0c2d18584f2e3c3793c5e1f06168c3793c7e2f022a6c3793c7e2f0a2660401d8de4f1f8bc3e062d3e4f1787c1c5968d45f278fc5e1f04fa37005085409e8de4f1f8bc3e0a2d545841007a3517c9e3f1787c14d1bc9e2f0f828b351bc9e3f17868b338210301548a35128540a8a20818b0b1617042c622f93c7e2f0f804f409fc9e3f1787c0c69c5027f278fc5e1f0516863793c7e2f0f804f3851c113198a39f278bc3e01a50c662f92c7e2f0f804f47161f278bc3e013b16663317c9e2f0f804f38a3c9e2f0f8068c59c2460898de4f1f8bc249194ec662f93c7e2f0d805143198be4f1f8bc36013d10793c7e2f089d8b33198be4f1f8bc3279c51e4f1f8bc232e2cec662f93c7e2f089e714793c7e2f08c98b3f8fc5e11d0cb8b30d051e4f178465c59c6628f278fc232e2cfe4f1f887032e2cde022c5a007c10f821d00245f04445f04407f0052763793c3e3f17818b438010301548a35128540a7214f46a2f93c3e3f1782871e802d042a7a3793c3e3f17828b401948a3512854005539007a3517c9e1f1f8bc028a48a08180aa451a8942a013d146a2f93c3e3f1781514380121e80222d8f40191740078f41081f41101f41101f41101d4111a30de4f1787c1109f0de4f0f8bc110344e6833f93c5e1f04c103419f0d85f278bc3e0a70d85f278bc3e09b0de4f1787c09099c10f93c3e2f0242534018c862309802067a30de4f1787c0909b0d85f2 else (if i < 22 then 0x1e0848fe00bc66588cbe4f1787c0e398cbe4f1b8bc3e099cce572384a9e2f03208733218fe4f1787c13f93c5e1f03965f042e672b90c6e270b8190478216431dcce5f258fc5e1f053e4f1787c0e597c9e2f0f83c72f8bc0c8b1c9e4f1787c163974be471f8bc3e099c1a5f278bc3e39b4c30f278bc3e09bc9e2f0f834b281021e183c70c00e068180be4f1f8bc287f055e4f1787c187941a0b8bc01034100733097c9e3f1787c053821069984b07f278fc5e1f05266f278fc5e1f00967b1f802c461fc9e2f0f80ef0d231187f278fc3e035c348c461fc9e3f1784eb0d214b099bc9e2f0f830f3793c7e1f01af0f319bc9e3f17870f34220fe4f1f8bc3e09c100733793c7e2f0f814b4b821040980fe4f1f8bc3e052d30883f8fc9e2f0f8278441fc9e3f1787c0a5a00fa38946e170460772c46632f93c5e1f0452718020cde4f1787c114a3c9e2f0f8032143319680401dcca3f278bc3e032d30883e8fc9e2f0f82784793c5e1f0451cd3820cc2303f93c5e1f019691a820cbe4f1f8bc312a0cbe2f0c4bc7e49811e389c8e37147038dc2a08c110998cbe4f1f8bc3129c520833793c7e2f0c4a833793c7e2897866f278fc5e133048cb38200ee550793c7e2f099a98441fc7e4f1787413c23c9e3f178624e59c10651001fc9e3f1784cd48200ee650793c7e2f099698478fc9e2f0c4a684793c7e2f0c49cd3820cc2003f93c7e2f09969f04204 else 0x0)))))
def lay511r10 : Packing := (2000,4,5,63,0,16,1,word511r10)
def keys511k11 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0x8c867d30e80000188bf832c42dc80003c3a9cb98022810fb000e4f0f081483cbf60b20000007081b0a02050f030101080a0308000b0207051605131c06010406086200050003013801060d05010e000a0e08031c0645050f02082b00020400240c0601070001050c12000164030b011410002003120012020002000a00000d0a1420000805140c13030f1912191d132504020200000a0f3b100c06120b010b023e0506000f0d0603030000030228000007123e030b008b1d24030c0c0017040408030d040d150100080001050a03002820612119051905040008022b080901041d0513040e331218000b0007770008008b0000000008370100170902232c1622050009010b0214042e231d0b1101440e040a0806020903211c0105021f083a0012043700003b112609000e00130e0224000800020e0756102f1b050b0b0319002709371200010800071e36050b0008060100b700060603080014030400090d1702031f1d00140007090417061901000100000300060300000c001507050c012301071c0602000706010603002c260b07030c001100040006070003021e04000c37030203060504000900010d6b040000040400160c040100031e252700012a02091904000a04031205000410000901010000020009e1090c00004d0202140020000103581f0d1681000107da00000003001836000400000505110e0e0a3200080507001a0f0703012901000301001304002b040a110a1d0e07002c001f000607091c1a12060703140002022905030200091401000e0000080102012c0202001c3f010a01050a090f10090a01160b01010a03030200080007170003140f0203090d0c11030006010200072b01010705320c0c041e28090e0a0b15021800050f08220000040722000100420b0e030800090201080224052900010b080701193e0201280e0001020300020119110b0600020e430003072800000006120a0925080d0200321405000d02012006080d0d2d01060d0b5000201c000d110104000d010904230001020216030200001404030000002f590f05027f1f01000300111e00102ba100400a0a0004073003112f00000500002411041810000201000a012882050b05080431000905000821090801100d003101070100020d120a000b0401032a00120f0c02000000000e00013200321328002007170a0a36000b00524c0c00000404030135080b0301063702050e01000811261d2101000f06050a0000220200100257030ba027081d56020c1c030207000101000301383a000003004008000300050b0109080103240203010c0c21242e000904040002050405000b0d0e00021d0900020f027d3738210a000c000014000a00140004031403001f000012030103043813000121080003290003010101130603010e00101a280101010500000d else 0x68dea88627279c07ac9ba2cbbbc463000068c7f95720000c3366989dcc9e0000e597d930207ff81a852722876841af226d0000096480001a3f7104b5544da0c840395186c2c28b554a15ec332dec3b4e868607c2ad40a051045e6b0f4a578eac0001e2b15110b9d08c38121e6504251dbdd30b243750fc7825e0cda745b83158804141801a4e349000003f7e00000e1e8783380001c6d70000653e3c7f3c8bd65930000000000000b216486ab060871b032fb80002e1f46e73000000000c3a5302f00004cfbd001800005947000000001836582ae00002471f66004137f1a0c5b8449c02eb8b9b500000837b0000495040000000000001889666160000200ba01e80001a4d4000069a796027c205d25d80002ee44000010da00002c9b200003182bd5a80000608313a408f16869741f3f4af72edea926a2d9d02f318f7e31e7daa32b89993845ea4c3881e1389d70c7d2427d0718ca1e6a51f3a4b855910bc406346e791b6000024d220000a2b1800000001d1b1a15cf9d1a859ac3367a83c0fabc259440262b088e6fcac021ca5390dd4a4608d065e0418bc1b7e641fd8f74d364c265b73082df3a9394f8ac016042f3922812a4dda86d9206ee294b032ceb8bb05328b9a0546c47c1230306834c07a375e05b2095307208b101123409360dcced6b0000509d8000000e52599d58974bd9e459525890e468146c62a9302e00a7c82d12fa300ac12b50e3ad15614ae9932844ffa62513556847f08a2c96718d1583f1ccb4852d25e8a96bc2330301ee874000020837764822904ec23eb6f97ac926d8de4250aae52c814d28759a1bf978b1a2fe166dd4aaeb0f24d4500f1872a864141bb3af65024103c1275800000d1aea8cd616848143008046b3135c58f53416600000000187140deae4040000000028e95c79e54b44868acd4f2966d6bce8e88c054c70c234068169a26906fe813a001f9b8d915c8edfc793a68a66011802b479110d0220a54612ab843842dd184b706282f4000000000f37b1c4ed4c1ba270f287481e0057d6c2c93c48b0c6ca34c3549b23084e47b2167acf2d261240000082ebe11260c440001e750602380000cd9dc1e4a3e6dde264738e006209f3177288136486c1d280917c516da6f00000000000000c25e3d400000000185e6000020380e785f503e3aaaac380000836983d985f134aaca69310b9111e34d562628b49280000851e02a700007c747eb8c8331311c58e28128e657a435290d33620a000033944b09dc908613c637d9ae848478e182c37a1171745420000816024bf80001238d63222126396a68105000061c00a181662328ce489ecd729c1af9d08a8fc4000130e52ad2805015309a4c7f098000034218c6dd341b312ff356dd7bc21fa0000000019aae62c50c15759d800001cb9dc9ec0001ed07518c823ed4d) else (if i < 3 then 0xc851b9094f8a918b7ec0133202b90cdc33d4251359861407468e80d580e1417ff842085d170c980001680b037d71faf13394625046e82fc000030a44000091ec187880b71c1b60000310072724a9584334d6fe50ee2245ac287e91cec36f2617601b6134804f803e89926555cd2311e521524feb238c92a00ab33afb8c00cb2d71bea8a49cfc508eaa0eee06101ef18a9e000042fecec7e8d48019472620996d0c97b5ec000000001403c0000000000003488c000098be80001870b4e6e2c42c1e8acabf270d52d664910000046bbc2f081877cf040000a29239ecbeb965b09e10c9909a085604a8f02a78af40001a68b427909a7fc2b2000047065d08c0001a0140000478b137dce70335e70192387f87e1b73a0b102a431d6716434811159013523ee20a6c90f5837ae4d663c938e7f4f41a23a62503240d475da0a0f119d17c0d934aa64d14dc11a344f3030c12d8c067d0aa742db40fea8d1bb61588253a9fa87e98f4264a717e3a0572631ae43255e51c95ecd82034f5267a88c30b0963649160e8ff649f5a33bcaba18bedcd644008d4dc32e74c70ec2936358e0add62d9c6ee7347cd05b96dec146076d79d7121b1420ce2e96187ad2dce0df9392b0ca38ca701df38943982a0071221161591184c5bdcd1b960f2f8c91c877832e737078158f5611e4cf5a6b856d50a5c52f41a0ba54ed1fa912d51ed10e59c325c8de31b3f1109830a033aa4398d4f5439f494e105ccf80f8c8d2fb96f3cfbef91b6dc615b71bb4f488410f01c63c748bd896cf625f3432f131542ae45353028a18db9a104624788e20f788767a4aac95b4452e51c4c0fa1ebc5851d8b932dae521ab623cc753ef36d04a48b710cc4c278e024e81156332c88c8409e95114c3561ecb0b4a5efe4d3080010282f81890def6687ca2ea018549b4d02eb2f3f85850e5a5eda747810172a2f84ba99493ce16d23562a6644bb2120e07706684c8cbea16250e427b0c1ae408b4cd6840c41a8ec0da1005923adf6f080002c9f8c181ad880a5a44333f12c83bfa9296d6b95ba20000511d98afb26de60b4287f9e33ae5a500002ce2b4290a2e2e9cee05b0abd5925d712401a22a7b6f852305fe072086c277b0509f884db8eee2beb4259de66de69af27841b1502b745bc48593daa6dca2a45427bf22cf9c6440001c48fb88f71dedccac951764d8e05d1049e31aedd87c066b0105e7aea24b02e3a4617e60f75d23431fa6622854000079d98c17c44c8d9544161942be0000614ca8e2e87c58562f121e1a054c3fc55501999a1bb61e4d13672b601951ca9dd4f48040a14e2e39607729144000025d67e630d131152461249501de339000006f5da1aec58328babd0d8ab880e36c968000008422a11e80000000084d7c16c7040747e0221df47200f440001d5a900007927542ce0000000 else 0xa2d59cf62e0550000089124554a0b2000018dbd8f7140fb504c8006a150800008023527942dd3c03df859cdea9a32be186000050970000063bb7cbc20ba7c5ee0000814c29c384bdca58d0000094a69b7e000000000000252ab682b98b700001c9fce449000023ad9441600000000411e80001a5e2a3ba5a9279a01278491f213f390a50cd0454cd087ae90c55e7842db3b6ea1e5bd6da3dfa80ab8c2e60000602701bb3c20ec6dc0067894c403dfe4a9e192bd4200000a8f1000051e05c42a66060061d8bc37b1c705253d7d0b0c474105c62226800039c70a51ce28400003074e0000a4bc28b87c22f687bc79a095a4000029e2000000000000186c471fc717c44b230580000012c6ec114817924eae813fd7980000962a5253ec53800000000211709d0f162c815a22d4a86a2821611d0cc4a8c58d83a38813c1cf988a4e123264b80000ce39e0ea91db244e68bfc0000d396291fe001f43e39092b142c00007ba0c1a980000c08867a9a0bb494764bb1e8b3b23b9f3bc0e7ea2ca918a28d670268463f834a0245800000000111b34146800903893c64a4641cf219355c212c84ec00000720982b1436e22a8a0d8000000001daf0a1fcc00b4c4ccd57d036ae2acac3b8ef9886f812fcf96ef3b03a492f08848ecb62c28b021198288af0c459b51f9c4751898f4de415b8a841d740000067e7191315fc000000008a91e01fccedb824202b771d2fef8120af605e64335c5acff16000040ae00001601c754f1019c00010d094063a98a5ca20cb630130b9d85c725bbaf00000000016cbe17df9ecf46970690c04800001122ea1b200008997d14cbe20c000002f980001cf3600000000276110bc000001490b80a2c34c000071663a604447c657b0000000028f18e2f200c01025509332063a3e391b280000ea60d05ec86b2cbd3e63a1cae80001048e253c7366d0000e294d155c9a82166b0e8fe47ec2a52c4c8d367419d032c1969c000023ce31038afe885507e5a0000683b5c0bec9b2f0a574d8af420302990aed9ab143dc0000b5f68c75504d711bfcae675e8c0000000031bf6eb69d53ae17800004a9140000d5c161e01170922d5257e70baf027c30c2514f52e710ddf0637c487915698f280000f6eab17fb0b4e0f7c2de0c24f693a1eb8a000060b6d0fcc000034220000789688e9a00000000000023046000031100000001c40465000078a9887cc000000007d17000000000e38928ebffce942fc0000338cf0cba0000414e80002fb32210255b000002447e0000e25a88ec4cacb6b1402aed8c9a9030a2da31419de215491c28ae03050e198c9475aa50a980000000180074981c076c4426a4dd01cc000036ae247c40021f8092029c857693dcc83f69712997490ab000010cc20000026f711aa4182525e000008ccb87b7c81a1032a0c07c25)) else (if i < 6 then (if i < 5 then 0x119f10abec11e834ea3add1047013890dae339c1e4daa3f86c58f275d6d8c5f1c356418464fc24a7ea294a1e7c0caf4a8a6d0c9377e9dc38a92232d0000282d3ce05869732958159888506e48510742cf42bc94589e1eeacc300037e2573363917202a6ac3c8f266015b6add8028ef4794185be2314a82c1e1e138847ad06a13c2adb4188b9e47734025c1426104731c9bd16b99f1cb1964e572f1c8475549ef581b23390f57a26004d551615cf2182397e18c01a2940286c10f249064698c70dc5b4040181950ab445dd1b6a20bb94f5c39903d3446cf8faccec87129097da22e97c7598510000315cc5c8ceada2203846dcd7edc72269d3d1072b9352ec0000039cf5dea1254636e48d7f9827460dbb37eb79464f5ba79f00000b39e89c0024e98e1c8552a18ac2ce000030ea00000e6215d1f000000f6a64fdc0a879872d227f3590154e07ffc2f8000076db88d6d474845f60037188130bd7a158d036704cfc20d63bf7143c5481ce9e000093260bf2b419bad150000480ff61cc65fc600560c3d03620000000071d6bc854e48ce895f0996934fe4f6d1a9710d80a24c2cba5b5c8c8f8f9f86504016a84904826a6cbe52e543be36a7bba1b06cd36cbc00a000000007aa818ed68502795099cd0495d2412000030a11525a441fa3c780003cd7ff78c00004ac128774055078d2018e1420163b5787f076b800000000e1283855529fc84f5160fa0a58ccc080ae0000110c3e5672491b388e0b1e216a3375000059a6f6c7501f700000000244d9eecd0000601ae4493872ee1298847ad2444022e293e10a5cb7c0000135a8050883ab031eda49000024e3005ea70d861cd400016cf5004900002e28e408604739862d035a70c21a03b8834c1e227cea33f810760caec8be1f14705130498a44300007c6b4c21ba252b924b00d799dc40cc427a41177592d9b6b425e967d8562d2023e0ee7b0762201037f219c285a80000031528d50000372ef7e4aa617011c743e4d11ac133e8f339bbb014f403e99bc4062d0964500e9c3858c93254d00004c96ba18700b10000000024b4595d3f06519b8e0b2f809b000000000c9046085ad82fc5179dfbe06af10d915e40001c05982d55196744800000e36d00db8abc588f9e1a5430a035ba9164519bc1f0c0001433d467fe90fc88d7e071489b9962f03bd9db55a82913e0c0a50b3253be80001abf7431db29dd2f1bcf2a08274516a944ec4c8864791d348625853e6685a237f1605a30775b5bbd5d42b00001879700004124e4cd084b7a10f747598d9342b591ee389a3cb5600000000314d26608c85000004806459ed60410000000000001e258000000003013ac08e0000184ab02624358152d4bdad03e0000000002843d005fa31cf1dcf029ecb9aa188000048783cf1a24b4000071bc397af840372fa else 0x14cc5c0e2b682cc79a0a8e27e447f173cafaa1bdad16bc244200b9d719e1219da6e98498b290203c2f7b4c7fd744036d9044b79ecd1baf2a604b9c86ac8f060000617244daf0468e00245d7d081ac5d86b5d52bc6d0af4e02a40da305c4383106e2458217a206cb0652571010d9a89bb011083fef19fa8f3647dadb0d301d125120ec0c397e1fd24d83800760ec0ad71887f87ca6601a16bca2f28025c91fb367c4705649647c5f134b0bfb8130eaff415e50bcf05ca03bc55511b6d34f6f674927aa993624b940000b874e1f06006e863451efa87a0e376497585e5906402a5611c2603873b31eead0b54266c7186000000000b3cb786d4ce5e91c8720d0d8a00000c49c335471104aebfa726c0ec7216e9214b1bc25371974c000020a425e90c66a0b8f2fc990dd48bf6f7df4277bb2512544085aeebf8946f01e74898c19ca0dc01ef74f3be27a83748ac4b84e695f6764cf9e9edf67e39ad0cbe03f9cdf9830a352756af800018289a9bcc198c5b67465f3064dc58f86af2515a85c39de6c26408cf03bf00003c2f4e256905ad0ea9c567873b2ae5101be1865cdd1ea7ef8f9dd1b5066a19f772132201e728825ad524ca86f9386d604f61ce51550e709c344c0e043362656f109aa2c478454208730f56e1ba8c7360dea1428000388aa0466312deddb30caa86666f04d156288c2cda8c03bc37051b00492c87ddb2e57081f4212a48ca3b3cc0f60000d1d861a347748cd7d30dfc0a5d6861e7444d6e3049c4c78840e0819a04e1c61de4ff93cc8000368c144c323086121704cdc0d1a113a252741e40000b205f90e949a680e13138b85facb39e540d81dc845b44954e44aa7cb872f275f6cea72fd1128ae0e2444a98cb5d49d0e622db5797e48fec0000c73785e69831848c4ab0cebcccc958000013df000022fb184faa16426bfb99080e1e8a5b82cf51db32224d05a328a087758a07a128e31681bcf9053daa5027651f2c04c60000d105698d5743f84530d22c913800000000d476b860d05618814a222f190ee168a1988181292878af8b0c6d88830b21e033c2eed0faf9290c879778d6251e8037f608330182af30e51c3f6eec2810a31b037205c4e762b588ef788f2000025eb0151e804b478aed588000211ec0000b0560000000002c2da9ba09b87c4656729000061dd585de23e1000020e7501fe68c452c280002aa0c00000586800026a37e674807349593a09a0000425e598bec559808bd1a680003d0bb00d0000029813ae4e93000000792388d15471e000050d8e0d6c3014922a70a08000021430000000022ae486d3421765436e25c0000000041d46c73dc4f131f01294e0d4025d012685bd0b068a0000259cf12e70de4c6df00006a09b8aa491ce19bd64ef03a12350460f3c9a4a84e558186297192d9460e70b16f139806205da) else (if i < 7 then 0x1c1f2e649755eae1831873b45f1c1d16163c9420363c5a4dd792abb09e9938789eec55184ad000000000c4af220c496864b82033500498a126138300f34097f9ccb454a2b36031d84fd54ef04374b03469e1ec8bce15a90dd9d5000001a32f00002186f8f74b18252936052c554c2202429d4a5305016c1bca026da65f031fe28d8292939d30101e317205d6297e8a9128cad1af4791924ee606da30428b7c01de84b2e15fa156dc1f2b7c57114e952ec34369290000201768228e5b028bda9d169555e11ac073ec7511542a2592589b1af68ce2249a828c885c3134b60b7f2edfd0beea0403704271800028689a9b761c1800018e6725c05275800024d2c13a000005efe854d27152d0e8826db13410f6a00002a184000160585df88f6c9c1e00000f1939461fd91fc09038b100001899a0000000011d5f6054684ee1501175b4be840b8f24d89c50ef7be162a05db1778098c58ca308aa05bd4d5c6380b3b3c5ccccb07a5888bb68a5eb468793876d568de9e5c92937ce0138c07f04bd0393338cb37010c198670b8e9b87b666a306c3b86e3816cc0afa32ae36dfcac68a8609a2a27331c564ea8a0ebf100188c70b89529067b4f00eed19243554b8b0e32c4066000091c7604445f8d86d1ca0588a1b4c4c7e592357e97690992271b45268000396d36daadd7fab438cbb382d5e3b1000034bf6a78002392306709f6b32e706e20a018ca59dd5d0d2f89fb8d44a7cce2919decb624a8075334639cf0000024105eeee930543888489511628e31356400000caf2435b0788d627f3e16a66d1824a5ba90fccc0b7ab85aa5841306af26fc9b42177723c964e0cf5614148a6492f9f625017b10e1ddf2788d3efba05262108c0001c8ffd0d4fafde822603d2259af9d5940d223b7f09ba08a291e7cb1f2a78119bfcdfe0000000041d950b97629161e5c861cca1930e44c27ec184e2e344805188000000000a60ee1834842a5d10c4b8810e00003887001d73608898dfc060b0213393800000e80e37123ddb99dab6220000247790d42091a01514786105df045ea4340000100468e6d650610b18000386817d80d28c5b450978f02bba17d48cd04cc9a20183e4d8a322e830b3ed372f03de986b036b780af46a50d7d60aad2c1717910edde58f5395313e40001705f0210d0fbdb9d457c2f21f0a5f6878cd1270000082840000936388b2e10e6cc416a51811301a398e9d6321f2d6923058896d22d506d00002ceb34b219084800000000000042e1d1e90e09c00005ed600000000120f624da396f40dab4614000059c136a5ea69503c2f0869cc640000dc90320b10732152ebd8654598373a00009ebff88d5234720a9d240b076511ee22e841e399be567d0a29ee304b947dd209a38256eb7129949b90557d11ba89a84c32e2c5b0d385edff46a271020a4d else 0x2c59e8152e1f49965400016587000001091525501be3364741748c66000020e70955000012706000022056bbae26bc0000000018588610ba1b371972c0c800001e38f87d34ea60999216a00003f202000042100803b95a4600be0104ad9acbd1a19b00003034d0122c66ba36600000000166ba2a120000255538611b00fc915c000046d0614afd739d32506d600006074ce0567167e81ae2f504df4e20900000000000002ce98258014c23b660000562100000000003be5aee9d6fa4984b35324b97726605c7a794a2b3ee57c81d106a92004b1c7e4929018db0d2046bfc473c33cbbb5e67dd261dd534a3e5283a48196441ef80912c2394e075f7b704111d18aeb614543d586b7925398a5600f8d4e864ebd0723724518904438e24ab10b8a1d30ea4a412d53e411a68c0657aa863c8800037b56a2c9000062173c0cc0667a33bd00990b518b8a000011ea9cf174730c0e6e1066ee3e000071aed1c216a4d81e181b98000109daa79c51a4a028aca6ce705506b491004da4d7ce579aa82c1ab012195773b23b794224284b2351ad6b009758a4a6107c125eb04fc073603a61903ce2f271a32952102389968320f20631123cba8a6e402d1c2d06e1c7c6d8f86439c286b8fe1e9c05476d5884ba67a55598b85314257e18aa585e9c1fe0636798a07221adcc37345bcd08210ce5d632cf0275a36878c00000000000041531804327c092320209312f724df931719d63c447ec0e51511a69365224379818480000000003b40000000034a14d06bb2f95dd8c21bde0d2059a084980626208c95318000000002dbb82cec2fd789a2957f12d3719d5c6b56aa4739c49eda62fd876390b280001c1e9835fd353112b34bcb407ce3da18eb2ef5a02d201fb2950900ed85a9a915a0de1d4cbb7c391b973037911f244f7288913ce4d32c2d1a17cf04674e574fb5000070a488098a76a2375000000000677ad2efce13ac5e3673ab0b314c1f0a2c6108ac6219e680001447dc04690f656524b52cc01f52427569366ad311d91e1a4d3851467481283524b67e16032bba54798d3b61f6c08df6d4b8308e16bcd85b76ff78dc0000a18d497b71d70a77cf33722af60056222290c888632ca7342baf3bb18b779c74000041c45dee0000163f2000000002173f86c20000015d28d72a5ae00005068f880007c6605299da40000304b120a03ce615b00000929bc1e8d120200008316619170f114103b0e4d916c569ea47ba34338f5fa2902866945ad0e104e16708c907c5092e0c055e4801a1585fe85572122482f00002a57c940a47a7b871804312)))
def cut511k10p0 (i : Nat) : Nat := 0x809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904
def cut511k10p118 (i : Nat) : Nat := 0x8090400000000000809040000000000080884000000000004088400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000009840000000000000500000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000809040000000000080904000000000009219000000000000921900000000000021088000000000002108800000000000808840000000000021088000000000002108800000000000808840000000000021088000000000004088400000000000210880000000000082210000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000040904000000000004090400000000000005000000000000000b0400000000000822100000000000080904
def cut511k10p1079 (i : Nat) : Nat := 0x2108800000000000210880000000000021088000000000002108800000000000210880000000000021088000000000002108800000000000210880000000000021088000000000002108800000000000210880000000000080884000000000002108800000000000210880000000000040884000000000008221000000000000905000000000000090500000000000009050000000000000905000000000000060280000000000006028000000000000602800000000000021088000000000006028000000000000602800000000000060280000000000006028000000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000c0b040000000000040904000000000004090400000000000409040000000000040904000000000004090400000000000c0500000000000008221000000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000040904000000000004090400000000000409040000000000040904000000000004090400000000000005000000000000000b0400000000000822100000000000080904000000000008221000000000000921900000000000030280
def cut511k10p1143 (i : Nat) : Nat := 0x4088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884000000000000160800000000000105800000000000092190000000000009219000000000000921900000000000092190000000000008090400000000000c0b040000000000090500000000000002108800000000000c0b0400000000000210880000000000021088000000000008088400000000000921900000000000080884000000000008088400000000000016080000000000082210000000000002108800000000000210880000000000021088000000000002108800000000000210880000000000021088000000000002108800000000000210880000000000021088000000000002108800000000000210880000000000021088000000000002108800000000000210880000000000021088000000000002108800000000000210880000000000021088
def cut511k10p1207 (i : Nat) : Nat := 0x809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000002108800000000000408840000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000005000000000000000c840000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000000500000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000080904000000000008090400000000000005000000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000040884
def cut511k10p1252 (i : Nat) : Nat := 0x11104022021085261110402202108526111040220210852620a100840409118a20a100040409116a20a804001600841220a8040016008416111040220210854220a100840409118a111040220210854211104022021085421110402202108542111040220210852a109108001121041a111040220210854211104022021085421110402202108542111040220210854220a80400160084161110402202108542111040220210854211104022021085421110402202108542111040220210854211104022021085421110402202108542111040220210854211104022021086821110402202108502111040220210850211104022021085021110402202108502111040220210852a111040220210854211104022021085421110402202108542111040220210854211104022021085021110402202108502109108001121041a109108001121041a1091080001210696111040220210854211104022021085421110402202108542109108001121041a20a120840c09118a20a100840409118a11104022021085421110402206108542111040220210854220a10084040111461110402202108542109108001121041a1110402202108542109108001121041a111040220210854220a100840409114642084408002a81d6111040220210854220a120840c09118a111040220210854210c08042080889461110402202108542
def cut511k10p1316 (i : Nat) : Nat := 0x1110402202108502111040220210850211104022021085021110402202108502111040220210850211104022021085021110402202108502111040220210850211104022021085021110402202108502111040220210850211104022021085021110402202108502111040220210850242084408002a8192111040220210850211104022021085021110402202108502111040220210850211104022021085021110402202108502111040220210850220a804001600841211104022021085021110402202108502111040220210850211104022021085021110402202108502111040220210850242084408002a81d61110402202108542111040220210854211104022021085421110402202108542109108001121041a1110402206108542242100840401114a111040220210854242084408002a8192109108101921041a42084408002a81d6111040220210854211104022021085421110402202108542111040220210854211104022021085421110402202108542111040220210854211104022021085421110402202108542111040220210854211104022021085421110402202108542111040220210864211104022021086421110402202108642111040220210850211104022021085021110402202108502111040220210850211104022021085021110402202108502111040220210850220a1008404091146
def cut511k10p1380 (i : Nat) : Nat := 0x111040220210854211104022021085421110402202108542111040220210854211104022021085421110402202108542111040220210854242084408002a81d61110402202108542111040220210854211104022021085021110402202108542111040220210852a111040220210854211104022021085421110402202108542111040220210854211104022021085421110402202108542111040220210854211104022021085021110402202108502111040220210854211104022021085421110402202108542111040220210854211104022021085421110402202108542111040220210854211104022021085421110402202108542109108001121041a1110402202108542109108001121041a1110402206108542109108001121041642084408002a81921110402202108542109108001121041a11104022021085421110402202108542109108001121041a1110402202108542111040220210854211104022021085421110402202108542109108001121041a109108001121041a109108001101041620a8040016008412109108001121041a111040220210852a111040220210854211104022021085421110402202108542109108001121041a11104022021085421110402202108542111040220210854211104022021085421110402202108502111040220210850211104022021085021110402202108502
def cut511k10p1444 (i : Nat) : Nat := 0x424402080822418e224205040921218e109108001121041a109108101121041a109108001121041a224205040901214a224205040921218e1142200021440862109108001121041a109108081121041a1110502202108542224205040921214a224205040921218e109108081121041a109108001121041a48088c0c0292819610c08042080889c6222410004282109a224205040921214e224205040921214e224205040921214e10c21104080921ce10c21104080921ce1124180602928216112418060292821611241806029282161124180602928216222410004282109a222410004282109a20c211040c09214e222410104282109a42086418082a825e112418060292821611241806029282161124180602928216222410004282109a10a13012082a81da10c21104080921ce22241000428210aa222410004282109a222410004282129a222410004282105a81120110021421ce20c211040c0921ce222410004282109e1110602202108542811211100614220e222410004282109e222410004282109e222410024382109e222410024382109e11105022021085421110502206108542222410004282109e111050220210854222241002438210aa222410024382109a222410024382109a222410024382129a222410024382105a222410024382105a48088c0c02928196224205040921218e1110402202108542
def cut511k10p1508 (i : Nat) : Nat := 0x22241002428210aa222410004282109e22241000428210aa222410004282105a11105022021085421110402202108542222810004302109a222410004282109a222410014282109a222410024282109a222410004282109a222410004282109a222810004302109a222410004282109a222410024282109a222410004282109a2440a0088614225e222810004302125a222410004282125a222410024282125a222410004282125a222810004302105a222410004282105a222410006292105a222410024282105a222410004282105a224205040921214a222410004282105a222810004302105a222410004282105a222410024282105a222410004282105a224205040921214a20c211040c09220e48088c0c02928196111040220210854220c211040c09220e111060220210854248088c0c0292819648088c0c02928196111040220210854248088c0c02928296112418060292829648088c0c0292815248088c0c02928196112418060292829648088c0c02928196109108001121041a11104022021085421110402202108542111040020210852a48088c0c0292829681240210041441ce11104022021085421110602202108542109108101121041a1110602202108542109108001121041a48088c0c0292829648088c0c0292819248088c0c029281d648088c0c0292819681120110021421ce222410004282109a
def cut511k10p1572 (i : Nat) : Nat := 0x1110402202108502222410004282109e222410004282129a222410004282109e222410004282105a222410004282105a222410004282105a222410004282105a11104022021085421110402202108542109108001121041a11104022021085421110402202108542111040220210854211104022021085421110402202108542111040020210852a224205040921218e1110402202108542245020088604209e11104022021085421110402202108542224205040921214a109108001121041a1110502206108542224205040921218e10a11002002a821a114220002104085e222410004382109aa0188850030409c6109108001121041a111040220210854211104022021085421110402202108542111040020210852a222810004302109e222810004302105a109108101121041a1110402202108542222410004282129a222410004282109e111040220210854211104022021085421110502202108542109108081121041a222410004282105a1110502202108542111040220210854210a11002002a821a111040220210854211104022021085421110402202108542111040020210852a222810004302105a111040220210854222241000428210a622241000428210a622281000430210a622241000428210a622241002438210a6222410004282109e111040220210854211106022021085421110402202108542
def cut511k10p1636 (i : Nat) : Nat := 0x111040020210852620a10084040111461110400202108526222810004302105a222810004302105a424402080822418e81240210041441ce11104022021085421110402202108542222410004282109e11104022021085421110602202108542222410124282109e224205040921214e222410004282109a222410004282125a224205040901214a4808840c02928192222418004282125a4808840c029281921110402202108502224205040901214a222410004282125a1124180202928296222810004302109e222410024282109e222410004282109e222410004282109e222410004282109e222410024282109e1110502202108542111040220210854211104022021085421110402202108542111040020210852a222810004302109e222810004302105a222410004282109e222410004282109e11104022021085421110502202108542811201100214220e48088c0c02928196222410006292105a1110402202108542222410004282109e222410004282109a224205040921214e222410004282109a1110502202108542111050220210854211105022021085421110402202108542111050220210854211105022021085421110502202108502222410024282109e1110402202108542222410004282109e1110402202108542222410004282109e111040220210854211104022021085421110402202108682
def cut511k10p1700 (i : Nat) : Nat := 0xa018885003040a061091081019210426a0188850030409c61110402202108542109108101921041a811201100214220e111040220210854211104022021085421110402202108502111040220210852a10910800112104261110402202108542109108001121041a1110402202108542111040220210854211104022021085421110402202108642111040220210850211104022021085261110402202108542109108001121041a109108001121041a109108101921041a109108001121041a109108001121041a109108001121041a1110402202108542109108001121041a109108001121041a109108001121041a10910810192104261091080011210426109108001121042610910800112104261110402202108542109108101921041a109108101921041a109108101921042a42084508802a81921110402202108502111040220210850242084508802a819211104022021085021110402202108502111040220210850211104022021085021110402202108502109108001121041610910800112104161091080011210416109108009161041610910810192104161110402202108522a0188850030409c211104022021085221110402202108522109108001121061610910800112106161091081019210616111040220210854211104022021085421110402202108542111040220210854220a1008404011146
def cut511k10p1764 (i : Nat) : Nat := 0x11105022061085021091080011210416111050220610850211104022021085021091080011210416111050220610852620c201040809214a111050220610852620a10084040911461110502206108526111050220610852610910c0011210656111050220610852611104022021085261110502206108526109108001121065620c201040809218e109108001121041a109108001121041a109108001121041a109108001121041a109108001121041a1110402202108542109108001921041a42084408002a81d620c201040809218e109108001121041a42084408002a81d611104022021085421110502206108542109108001121041a109108001121041a109108001121041a109108181921041a109108001121041a109108001121041a109108001121041a109108001121041a109108001121041a109108101921041a1091080011210422109108001121042220a8040016008416109108101921042210910800112104221110402202108542109108001121041a109108001121041a20a8040016008416111040220210854220a8040016008416109108101921041a1110402202108542109108001121041a1110402202108542111040220210868211104022021085021110402202108502111040220210852a109108001121041a1091080011210416a0188850030409c620a804001600841620a8040016008416
def cut511k10p1828 (i : Nat) : Nat := 0x109108001121041a109108001121041642084408002a81d61110502206108542109108001121041a10910800110104161091080011010416109108001101041611104022021085421110402202108542111040220210854211104022021085421110402202108542111060220610854211104022021085421110402202108542109108001121041a1110402202108542109108001121041a11104022021085421110402202108542111050220610854211104022021085421110502202108542109108001121041a109108001121041a109108001121041a10910800112104161110402206108542a0188850030409c61110402202108542109108081121041a111040220210854211104022021085421110702206108542109108001121041a1110402202108542109108001121041a11104022021085421110402202108542111040220210854242084408002a81d6111040220210854211105022061085421110402202108542111050220610854211105022021085421110402202108542111060220210854211105022061085421110402202108542111040220210854211104022021085421110402202108542111040220210854211104022021085421110402202108542111050220610854211105022061086421110402202108642109108001121041a11105022061085022440a0008214225e1110502206108502
def cut511k10p1892 (i : Nat) : Nat := 0x109108001121041a109108001121041642084408002a819210a11002002a821a111040220210860211104022021086021110402202108602111040220210860211105022061086021110402202108602109108001121041a11104022021085421110402202108542111060220210860211104022021086021110402202108602111040220210864211104022021086421110402202108542109108001121041a109108001121041a20a100840409118a11104022021085421110502206108602111040220210860242084408002a81921110602202108502111040220210850210920800114104161091080011210416109108001121041620a100840409114a1091080011210416109108001121041620a100840409114620a100840409114620a100840409114620a100840409114642084408002a81921110402202108522111040220210852211106022021085221110402202108522242100840441114610910c001121061610910c001121061610910c001121061611104022021085221110502206108522111040220210852220a10084040911461091080011210616109108001121061620a100840409118a109108001121041a109108001121041a109108001121041a109108001121041642084408002a8192109108001121041a109108001121041a20a100840409118a109108001121041a109108001121041a
def cut511k10p1956 (i : Nat) : Nat := 0x109108001121041a109108001121041a109108001121041a109108001121041a109108001121041a811201100214220e109108001121041a1091080011210416109108001121041610910800112104161091080011210416109108001121041610910800112104161091080011210416109108001121041e1091080011210422109108001121042242084408002a819242084408002a8192a0188850030409c6109108001121041e42084408002a8192109108001121041e42084408002a8192a0188850030409c6111040220210854211104022021085421110402202108502111040020210852a1110702206108542109108101121041610910810112104161110602202108682a0188850030409c611104022021085421110402206108542109108001121041642084408002a81921110402202108542109108001121041a109108001121041a11104022021085421110602202108682109108001121041a
def word511r11 (i : Nat) : Nat := (if i < 5 then (if i < 2 then (if i < 1 then 0x67fda726165cff66098596feda226165cff2a6885973fe99a2165edf296885967fca9a21659ffaa9975973fe8865d65d7f65c97596ff5a125d659ff6a5875967fca961d65cff26186596dfda721965bef69086596fdda321965bfb68886596ff5a121965bfe680865976fe995d965ebfa2176597e7ca55d965dbf662665976fc9899965ebfa2266596efda799965dbf65e6659777ca961565ddfa6585597e7ca661565f9f5d985597e7e66615659ff6a5855967fca961565bbf299855967fda95d565bbf299755967feaa660659ff699981973fd98a20659ffaa9971973fe8865c659ff6a5871973fd9861c65d7f65d871967fda921c65dbf66266197afe8899865dbf65e66196f7eaa59465ddf66165197b7e8859465def6a1941977be8865065def69d941977bd8765065def21d941977bd8665065def5d994196f7da625e55f5f2a677956f7da825a55bdf69c96957d7e7725a55fdd68496956f7eaa61a55bdf2a586957d7e7761a55bdfaa88695777da921a55bdf2a486956f7da721a55f5f69c86957d7e7721a55f9f61886957f5da321a55fdb68886957f79a021a55bdfaa976956f7ca95da55bdf6a176956f7ca85da55f5f61d76957e7c965da55bdf6a076957d7d761da55f9f2a666957e7da899a55f9f2a266957e7c9899a55f9f69e66957e7ca799a55f9f25e66957e7d8799a55f9f21e66956f7da899a55bdf2a266957b7e8899a55bdf69e66957d7e7799a55f9f25a66957e7d8699a55f9f21a66957e7d7699a55f9f1da669567fca99de559ff6a0969567fda725a55d7f9dc969567fca961a55b7f69c86956f7da521a55bf768c86956feda221a55bfe680869567fca95da55dbf25976956f7da51da55bfd684769576fca999a55dbf26266957afe8899a55f3f9de66957e7da599a559ff2a666956f7da599a55bdfaa975957d7e775d655bdf29975957e7e665d655bdfaa965956f7da859655bdf2a165957b7e8859655bdf69d65957d7e7759655f9f5d965957e7e6659655abfaa98621b2fe9961886e9f6199521badd8664c86ebe6199021b2fd9826266d9f6549599ad7eaa5d475f1f999751d6e7ca661565b9faa965197a7e8859465e9f61886957c7d761da559f768e9961a77eaa65486d5f65d9521a7deaa64c86db76199321b75d9564c869feaa99021b3f98664086d7e65d9021b7799564086dee6519021b7d99364086dfa6499021b7f19164086bbb6889599ae7da521a66bb768c8699aef5a121a66bbe6808699a6feaa658759bf6a6661d72fd98998759f7aa9931d76de6664c75cfea21901d76fa66640759fe682995967eda2261659df2a5855967beaa65065cefa21941976be6665065bdd68496956d7da721a55bd768c86956f6da221a55bde68086956f75a11da55e9fa2266957c7e7799a559fd684969572dd8664c86 else 0x5fdf25986957f7da721a55fdf25c86957f7d8621a55fdfaa976957f7ca95da55fdf6a176957f7ca85da55fdf26176957f7d875da55fdf25976957f7d865da55fdf21976957f7c981da55fdf61876957f7ca999a55fdf2a266957f7c9899a55fdfa2266957f7ca799a55fdf25e66957f7d8799a55fdf21e66957f7d8699a55fdf5da66957dfca69de55dff9dc96956ffeaa61a55dff2a586957dfe7761a55fdf69586956ffeaa21a55bff69c86957dfda721a55f7f9dc86957efd8621a55fdf69486957fdda321a55ffb68886957ff9a021a55bffaa9769577fca95da55bff6a176956ffca85da55dff26176957dfd875da55fdf69576956ffda81da55dff26076957dfd761da55fbf6a266957efca899a55fbf69e66957efca799a55fbf61e66957efc8799a55fbf9de669577fca999a55bff6a266956ffca899a55dff26266957bfe8899a55bff69e66957dfe7799a55fbf61a66957efc8699a55fbf5da66957efc7699a55fdf29975957f7d865d655fdf21975957f7d765d655fdf99975957f7ca859655fdfa2165957f7ca759655fdf61d65957f7c8759655fdf9dd65957f7d8659655fdf21965957f7d7659655fdf1d965957f7e6659655ebfaa98621bafda561886ebf2958621bafd8665486ebf618865d7afd8621875f5faa9751d7d7da65d475f5f299751d7d7d865d475f5f219751d7d7e665d475ebf61886597e7eaa59465f9f6a165197e7ca859465f9fa2165197e7da759465f9f29d65197e7d8759465f9f21d65197e7d8659465f9f5d965197afd8621a55f3f5d8769576fda6a65869ff6969961b7dda3a6586bf768e9961b77d9525586bbfaa98621b77eaa65486ddf69d9521b77ca765486ddf6199521a7feaa65486bdfaa99521b5fd9765486df76199321b7dda564c86df76559321b7f9a764086dfe6199021b7f9a564086dfe65d9021b7f99564086dbf6609899aefda526266ebf6a68899bafca9a2266bbf2a19599bafe8865666bbf6a09599bafe8825666bbf69c9599a7fda526266bbf6989899bafda6a2266ebf29a8899a7fca9a2266bbf69a8899aefeaa61a66bbf2a58699bafe8861a66ebfa208699aefda521a66cffa219599aefda625666bfb6889599a7fda6a65759ff6a0965d76fd96259759ff2a5865d67fda921975bdf694865d6fdda321975bfe680865d76fca999975dbfa66665d76fc9899975ebfa22665d67fca999975dbfaa9961d76fda865875dbf2a1961d67feaa658759ff6a5861d76fd96618759ff6a4861d76fd9621875bdf694861d6fdda321875bfe680861d76fd9899875ebfa22661d73fd9899875dbf65a661d77dda664c75df7619931d77dc8664c75df7999931d77fa8864075dfe619901d77f88664075dfe999901d67fda8a65659ff69e9959777da5a6565dfe68299596ff9a0a65659ffaa99859) else (if i < 3 then 0xd6ffda825975dff660965d77fc9825975dff658965d6ffeaa61975dff6a5865d6ffca961975dff2a5865d77fe9961975bffaa8865d77fda921975bff2a4865d77fe9921975fbf618865d7f7da521975ff768c865d7ff9a021975fbf6a6665d7efca999975fbfa66665d7efda899975fbf2a2665d7efd9899975fbf262665d7efda599975bff2a6665d77fca999975dffa66665d6ffda899975bff2a2665d77fc9899975effa22665d7efd9699975fbf25a665d7efd8699975fbf21a665d77feaa65875dff6a1961d77fca865875bffaa9861d77fda961875dff659861d6ffeaa21875dff6a4861d77fd9621875fbf618861d7f7da521875ff768c861d7ff9a021875fbf6a2661d7efca899875bff6a2661d6ffca899875dff662661d7bfe8899875dff65a661d7efd8699875fbf21a661d77fda8a6565dff69e99596ffda8a6565bff69e995977fca766165bffaa8985977fe9926165dff66098596ffda726165fdf69498597feda226165eff6a688597bfca9a2165effa6688597bfda7a2165eff29e88597bfda6a2165eff29a88597bfda5a2165bff2a6885977fca9a2165dffa6688597bfd98a2165eff26288596ffda7a2165bff69a88597f7ca5a2165dff2a1975977fe8865d65bff2a1975977fc9865d65effa21975977fe9925d65bff6a0975977fd9825d65dff26097597bfe8825d65dff2a5875977fe9961d65bffaa9865977fe9961965dff66186597bfc9861965effa21865977fd9761965fdf295865977fe9921965dff66086597bfe8821965bff69c865977fd9721965fbf61886597efca95d965fbfa6576597efd985d965fbf26176597efe885d965fbf695765977fe995d965dff661765977fc985d965effa2176597efd865d965fbf21976597f7ca55d965fbfa6666597efca899965fbf66266597efc9899965fbfa2266597efca799965fbf65e66597efc9799965fbf61e66596ffca899965dff662665977fc9899965effa22665977fd9799965fbf61a66597efd7699965fdf25d85597f7ca661565fdf61985597f7c8661565fdf5d985597f7e6661565fbf5d985597efe6661565bff2a1755977fc985d565effa2175597efd765d565fbf999755977feaa66065dff69d981977fca766065eff69e88197bfca7a2065eff69a881977fd98a2065bff69e88196ffda6a2065dff2a1971977fe8865c65bffaa9871977fd9861c65effa2187196ffda621c65bffaa9861977fd9861865effa21861977fd9761865bffaa976196ffda85d865bff2a1761977fd985d865effa2176197dfd875d865fbfa2266197efd8799865fbf21e66197f7eaa59465fdf6a165197f7ca859465fdfa2165197f7da759465fdf29d65197f7d8759465fdf21d65197f7da825a55fdf69c96957f7eaa61a55fdf2a586957f7da761a55fdf29d86957f7c9761a5 else (if i < 4 then 0x86fff2969961bffeaa65586fffa659561bffda765586fff29d9561bffd9765586fffa649561bffd9725586fff25c9561bffeaa61886fff6958621bffca561886fffaa99521bffda765486fff29d9521bffda526266fff2a68899bffeaa61a66fffa218699bffda561a66fff2958699bffe8825666fff6a0965d7ffc9825975fffaa9865d7ffda961975fff2a5865d7ffe9961975fff659865d7ffc9661975fff695865d7ffda921975fffa64865d7ffd9621975fff618865d7ffda521975fff2a6665d7ffe9999975fff2a2665d7ffd9899975fff262665d7ffe8899975fff65a665d7ffd8699975fffaa9861d7ffd8621875fff2a2661d7ffe8899875fff61a661d7ffda726165fff69898597ffca9a2165fffa6688597ffd98a2165fff29e88597ffca6a2165fffa2197597ffc9825d65fffa2097597ffda961d65fff2a587597ffe9961d65fff69987597ffca661d65fff69587597ffeaa61965fff2a586597ffe9961965fff26186597ffe8861965fff69d86597ffca761965fff65d86597ffc9761965fff69586597ffe9921965fff66086597ffd9721965fff25c86597ffd8721965fff2a576597ffe995d965fff66176597ffc985d965fffa2176597ffd865d965fff69576597ffe9999965fff66266597ffc9899965fffa2266597ffd9799965fff25e66597ffd8799965fff61985597ffc8661565fff5d985597ffe6661565fffa2175597ffd875d565fff61975597ffc865d565fff5d975597ffe665d565fff29e88197ffeaa61c65fffa2187197ffda661c65fffaa986197ffe8861865fff69d86197ffca761865fff61d86197ffc8761865fffaa976197ffda85d865fff2a176197ffe885d865fff61d76197ffeaa61a55fff69d86957ffca761a55fff9dd86957ffda721a55fff9dc86957ffd8621a55fffaa976957ffda85da55fff2a176957ffd875da55fff61976957ffc865da55fff61876957ffca899a55fffa2266957ffca799a55fff61e66957ffc8799a55fff9de66957ffd8699a55fff5da66957ffd8761965dff69a9961b7fda5a6586dff2969961befda6a6586bff6969961bfdda3a6586bffaa99561b7fe9965586dff65d9561b7fe9925586bff69c9561b7fd9725586dff25c9561bf7d9525586fbfaa98621befda561886fbf2958621affeaa61886dff29d9521b7fd8665486fdfaa99521bf7da765486fdf29d9521affeaa65486dff65d9521befda526266fbf2609599befc9725666bff6949899bbfca9a2266eff69a8899bbfda5a2266eff2968899affda6a2266fbf29a8899befeaa61a66fbf2618699befda561a66fbf2958699affeaa61a66effa218699b7fe8865666bff6a09599b7fc9825666effa209599affda725666dff25c9599befd8625666dff69a995d6ffda6a6575bff2a1965d6ffeaa25975dffa64965 else 0x2713c70ce70b0709a70446ff66fb86f726f146ece6e706e5a6e046dae6d686d126cfc6ca66c306bca6b646b1e6b006ada6a846a6e6a2069da69c46956690868ea68ac685e681867c26764671666b0665a65fc65ce6570651a650464e664c864aa6494646e6450643a6424640663b86362630c62ee62a0627a622461de61986142610460ae606060125fec5f9e5f485f2a5edc5ebe5e705e2a5de45dbe5da85d9a5d445cf65cb05c625c045bae5b585b325aec5aa65a585a4259e459965958590a58b4589e585858425824580e57f857da57cc57be57a8579a578457765760574a572c571656f856ea56cc56ae56a0568a566c564e5638561a560c55ee55d055b2558c556e55585542552c551e550054e254d454b65490547a545c543e542053d25364531e530052da527c521e51d851b2519c514e510050b250644ff64fa84f524ef44eae4e684e4a4df44dae4d984d824d644d464d284d0a4cec4cd64c884c2a4bd44b864b704b1a4b044ae64ac84aaa4a8c4a7e4a604a3a4a1449fe49e049ba499c49764948492a490448e648b0489a487c48764870486a4864485e48584852484c48464840483a4834482e48284822481c48164810480a480447fe47f847f247ec47e647b0476a473c470e46d8469a464c45fe45b04562450c44c64478443243ec43a64358431242cc42864240420a41c44176412840ea40a4405e40183fd23f843f3e3ef83ec23e5c3e0e3dc03d823d2c3cee3ca03c623c143bd63b803b2a3aec3a8e3a4039ea399c394e390838ba386c381e37c03782374436fe36b8367a363435de3598354234f434a63460341233cc337e3348330232b4326e323031fa31b43176312030ca3084304630082fca2f7c2f462f002eba2e6c2e2e2dc82d8a2d542d162cc82c8a2c2c2bde2b902b422afc2ab62a682a2229dc299e2960292a28ec289e2858282227dc27962760271a26d4267e262825e22594254e24f824a22454240623b82372232422d62288224221fc21b621782142210c20c6207020321fdc1f861f381eea1ea41e6e1e281de21da41d6e1d181cda1c9c1c4e1c101bd21b7c1b361af81aba1a7c1a3e1a0019aa196c192e18e818aa186c181e17e017a21764171e16d8169a1654160e15c81582153c14fe14b81472143413fe13b01372132c12e612a8125a120c11c61180113a10e4109610480ffa0fb40f6e0f200ed20e840e3e0e000dc20d7c0d2e0ce00c920c540c160bd00b920b540b160ac80a8a0a4409fe09b809b209ac09a609a0099a0994098e09880982097c09760970096a0964093608f008b2087c084e081807e207b4077e0748071a06e406ae06800642060405ce05980562052404de04a0046a042c03f603c00382034c030602d0028a024c021601d0018a014400fe00b0007a003c00060000fff69a9961bffda5a65))) else (if i < 8 then (if i < 6 then 0x521189d17938f8b878290745e4e3e2e1e048a31b938f8b878316766e4e3e2e1e0c59d9917938f8b83849e80e2745e4e3e2e1e00da4a09b938f891783849e9282726e4e3e2e1e085a41b938f8b878216705e4e3e2e1e0279c9e1a178f938b87828e4e3e2e1e0850d9c9b938b8f878036705e4e3e2e1e0289ca29a1e17938f8b8782928e4e3e1e2e00d9c9a1f938f8b86178280726e4e3e1e2e085a01e9b938f8b878216800000000000000000000063e4e2e1e09436221f938f8b878280807e4e3e2e1e09f938b878064526e4e2e1e01997938b87802052688e4e3e2e1129b8b93878c4a508e4e3e2e1129b938f8b84204a6e3e2e11a129453938b84204a61308e4e3e1129b938f88604a5872f25e4e3e1e09ca01f938f8b8782728e4e2e1e014981ce3938f8b82628e4e3e2e1129a1a17938f8b878270746e4e3e2e1e045a11917938f8b8782786e4e2e1e0109a421a17938b8782786e4e3e2e1899a1b938f8b862660d60c5e4e3e2e19f1423938f878260d0807e4e3e2e1e0a21f8f8b8780466a4918785e3e2e1e0a2441e178f8b878272785e4e3e2e098a09f17938f8b878286328c534e4e2e1e0a188a314cf938f878286028c532e4e3e2e1a184db149c9b938f8b829c5e4e3e2e1e0999b17938f8b878270785e4e3e2e098092ce92c892c292bc92b692b092aa92a4929e92989292928c92869280927a9274926e92689262925c92569250924a9244923e92389232922c92269220921a9214920e9208920291fc91f691f091ea91e491de91d891d291cc91c691c091ba91b491ae91a891a2919c91969190918a9184917e91789172916c91669160915a9154914e91489142913c91369130912a9124911e91189112910c9106910090fa90f490ee90e890e290dc90d690d090ca90c490be90b890b290ac90a690a0909a9094908e90889082907c90769070906a9064905e90589052904c90469040903a9034902e90289022901c90169010900a90048ffe8ff88ff28fec8fe68fe08fda8fd48fce8fc88fc28fbc8fb68fb08faa8fa48f9e8f988f928f8c8f868f808f7a8f4c8efe8eb08e7a8e448de68db88d7a8d1c8cce8c788c1a8bdc8b9e8b908b7a8b5c8b468b008aaa8a4489f689b88972892488b688a0888a8874882e8818880a87ec87d68778876a874c872e8710870286a48686862885ea85a485968550850a84ec84ae8460841a83cc838e834082ea828c824681d8818a813c80de807080227fd47f867f187f0a7ebc7e867e507e327e247e067df07dda7dbc7dae7d887d327ce47c767c287bda7b6c7b567b387b227b0c7af67ab87a7a7a3c79ee79b0796a791c78d678907882783c77f677b077927774772e76e87692767c762e760875f275a4755e751074b27474742673d07382732472e672a8729a728472667240722a720c71f671d8718 else (if i < 7 then 0xe3e1a0211d1b17938f8b8782908e4e245e3e1e09c38341814a01f17938b838f86c0ee4e3e2e1e00d9c23938f878b826e4e3e2e126e00d9d8714da349b938f8b8290ee4e3e2e1e00d9c1814201e9b17938f8b8782b0d87c5e4e2e1e0e308a43b14a01f938f8b87829c6c564073ae3e2e1e0a71b14a3938b8780528c6c528e4e3e1e013a31b15841ce3938f8b829c6c528e4e3e2e112a01c1b9386178f838a8e4e186e385e2e09cbb9385178f8b82746e4e2e3e1e09b938f8b87801d2274887c6c5e4e3e2e1e0a5181787938f8b801e848e4e3e1e2e0991f938f882383843688705e2e4e3e0e10da3938f8b878036605668de4e3e2e1e0a2221793881f8f8782806852847e4e2e3e1e00da81a14201f938f8b878036ae4e3e207e1e0850da0211c9b938f878b8036907e4e3e2e1e0850da038201a1f938f8b878216a0e06080785e4e2e1e0e3a821191f938f8b87811690687e4e3e2e1e0850ea4221a1f938f8b87821694745e3e1e0e4e20ea01a991f838f8b87911690847e3e1e0e4e2450ea4a11c9b938f8b87811694607e4e3e2e1e045a1221f938f8b87831684807e4e3e2e1e045a21793878f8b821e7e4e2e1e3e0079b93878f8b821e666a487e2e0e3e111a19a91a2461e178f8b8782a6687e3e1e0e2119c46919a461e17838f8b86a91a4688785e3e2e1e066a99a46901e178b87838e966a4910785e1e3e0e2a4a09b8f879382178a8e4e3e2e1e045989c9b938f8b87821682827e1e4e3e2e085a09a17938f8b87827e4e3e285e0279834a09c9817938b87838eae4e3e2e1e0450d9c9a17938b87838e70d2628e4e3e2e1e027a4a3938f8b87809e728e4e3e2e1e0279c34a09c9b17938f8b8782ac528e4e3e2e1e027a09a17938f8b87827c5e2e0e4e1e3289f14a3938b8780d27c528e4e3e1e0339f14a3938f8b84ca70d282705a6e1e4e3e0e2ab938f8b8781143670d05e1e0e4e3e29c9817938f8b8780a282827e1e0e3e4e29c9817938f87838a70d0527e126e4e3e2e0a71793878f83889e766e4e3e2e1e0459d9b938f8b87809e7276645e4e1e3e2e0a09d9917938f8b8782866e3e2e1e0e4279c9d1793878f8b819a82745e4e3e2e1e066a09d9917838f8b879282745e4e3e2e1e066a0349b8b83938f849e805e4e1e3e2e0289ca29b17938f8b878280d28e3e1e0e2e427a19b17938f8b87827e4e3e2e1e027989d9914a3938b87838e945e4e3e2e1e0279c9d159b87938f838a82745e4e3e2e1e066a09b938f8b87803670e0607e4e3e2e1e085a422178f8b87801f903a90685e4e3e2e1e087a03917938f8b87803682827e4e3e2e1e0c5a098a09d17938f8b878036ac6632834e4e2e1e0c5a71988a0cf938f8783169c6602832e4e3e2e1c5a5169b938f8b8780368a60745e4e3e1e0e2a0a09b938f8b87811436961362726e4e3e2e0c5a else 0xe1e0e248a1221f87838f938b1680d60e28d20349c9b87938f8b8316a45e4e3e2e1e048a6a01f16245278923811634564278d1b8116364a0458d1a8116366c589211917938f8b87809e90d48c626e4e3e2e1e0c5272c341f1b93878f8b8314a2aa60745e4e3e2e1e048a61f1620d2846e3e2e1e0e4c527aa1f16263a0458c1e8116362a0458d1a811630d04358f0230d2705c09034998a164c0278834178230da028859034178230d64c0a09034981702825c0a0268c358e8216405c0a08c341c998a82166c0a08816801c30000000000000000000000000000000000000393878f8b812260605e4e3e2e1e00da18f938b8782563e4e2e1e09497938b87838e687e2e0e4e3e1889c96221f938f8b8780369888766e4e3e2e1e00da6221c37938f8b87819a90d660807e4e2e1e0e3a43816221f938f8b878036a0588e4e3e2e1e087a03a94201f938f8b87829666508e4e2e1e014a19997938b8780645286665e4e2e1e00814a196819a2387938f884a9666508e2e4e1e312a1999623938f8b844a8656608e4e3e2e112a19997938f8b84204a8e2e0e4e3e1289898a0978b938f83868286665e4e3e2e1e047a4a11d9997938b87838e907e4e1e3e2e0289e9a97938f8b83861e80726e4e225e3e1e0a0a21f93878f8b829682826e4e3e2e1e025a01a1f938f88238780369072625e4e2e1e0e3a19997938f8b8780a28e4e3e2e1e0479838341c1814a11f938b87838ec472625e4e1e3e2e028a4a098961f938b87838e907e4e1e3e2e0289e1e9a94a01f938b87838ea28e4e3e2e1e0879c9894a01f938f8b8782986e4e3e2e0e1879ca0981c97938f8b878292f25e4e3e1e0879c2038371b17938f878b82a0e0dc6c5e4e107e3e2e0ab938f8b87803836706050807c6c5e4e3e2e1e0aca09c3b938f8b8780369282706c6e4e3e2e1e00da98f1b14a0d3938b8782960c6c52832e3e4e2e1a5211917938f878b8284807c6c5e3e4e2e1e0a41d1917938f8b87812294887c6c5e3e4e2e1e0a4209c14371b17938f878b82b8685e4e3e2e1e09e1a17938b87838e7688685e4e3e2e1e0a0221b938f8b87821684645e4e2e1e0e39c211b938b87838d168282707e4e3e2e1e04645aaa11917938f8b8782828270d45e4e3e2e1e0c6a8a18cd31b938b8783169286032c6e4e3e2e1c5a41d1917938f8b878284887c6e4e3e2e1e0c5a69d1917938f8b87828482746e4e3e2e1e045a61b93878b8042610908685e4e2e1e0a1a19e421a17938b8782967908685e4e2e1e0a1a21b938f8b8626786e4e2e1e38999a19e1b938f8b862686786e4e3e2e1899c381c183717938b838f86a0d0806c5e4e3e1e0e20ea837938f8b8781151e8c560e4e3e2e10d9f1583938f8b843670ee4e3e2e1e00d9c1f17938f8b8423803a9e4e3e2e1e00d98a3158a37938f87828474645e4e2e)) else (if i < 9 then 0xa038211c9917938f878b8036ba2e088391617938f8b8780369aa8d07050d26e4e1e3e2e0aa17938b8f8780369a8470d8545e4e3e2e1e0a6aa1782247c5080645e0e3e2e1e4a934221d1c1a15143837838f8b8792e28c62688870dc5e4e3e2e1e0b29918361d142217938b87838eca64645e4e2e1e0e3a0341f823a3c0608590389a14342393878f8b82ae34588211837938f8b87821e9460de4e2e3e1e087a3021e20e0dc5282e074626e4e3e2e1e0b4203837938f878b821e908c0458c9b93878d178b82707e42ee3e185e2e04da592178f8b849b813682e4d264585e4e1e3e2e0a8b9361899161793878f8b82b266463614562602e4da435201d143a9a1787938f838ac28850e0d06e4e1e2e0e3a83614381f8517938f838922b86a2c0608594b9361a14991793878b838eb2e4d86e4e185e3e2e007ab891620745e08c1d238236361e08c1f82245c0a048901d1b82362e0881f82264c0a08f181f9037878f8b80a2928a64685e4e2e3e1e087aa9a1517938f8b8781221ea85c0870d209a17938f878b821e963c0a04591189a179385178f8b801eae4e3e205e1e00d66a017938f8b8384351e8660d080705e4e2e1e0e3a823938b8f87811e72866058d07e4e3e1e2e0a8a19817938b8f87811e94626a4e3e2e1e0858da41e87021648685e4e3e2e1e0280da43a1e17938f8b87812036ac086858e928e8a86801a14ba369c086858ca19a1f938f8b8782169668785e2e0e4e3e1a21f938f8b8782159a84562e008911782247841e991b91178f8b8780a2a0e07e4e3e1e0e2c528a49b938f8b878314a28268785e4e3e2e1e00ea6183a1c982217938f8b8782b2807260ee4e3e2e1e0c5a82298191f8b838f879116a0885a460909b1783938f8b851e826c5e4e3e2e1e087a299181d17938b83878e9a3608820381d189917938b87838eb0e28c5e4e3e2e1e087a43b8783938f8b1670ec5e4e3e2e1e02887a4a018381d1793878f838aaa287883b1787838f938a1e848c589159282345a088178226361608e16187858982285841d92266849e162278588a09f8e345e389918b8e3e3849a8d16327a3458c9e126458a158f0232726e28f891626463e28f8a128a2458d92889a327a2458d8e8b009a445a2278c991626327889d1622784a09d16328c0278c9e12745668c9993009e4276688a18c9c32662270d1c991630e85e4e3e2e1e06687a620a21c9f189837938f8b878316d0d46e4e2e1e045e3a28d821630d6160e3903718a09b938f8b8783149eb0d46262827e4e3e2e1e0c5ac23938f8b8783149e887266085902316208c6e4e3e2e1e04527a450231b938b8783149e91308c6e4e3e1e0c527a448231b938f8b87149e90e28872786260de4e3e2e1e0c5b438352387938f83891694887860de1e0e4e3e2c5a8361e189b938f8b878314a2b0e45e4e3 else (if i < 10 then 0x8f8b87829e4e2e1e0e3659923938b87838e6080726250de4e2e1e065e3ad8f938b8782526a5e4e2e1e0e39d211e99983697938b8f8782b0e0d2625e4e2e1e0e3a435211d9b938f8b878296a080766260e25e4e2e1e0e3ac3b8783938f8a967e4e3e2e1e066a59f8e107e3898d858230765889897938f8b87821e88887e4e3e2e1e025660daa199a143494201f938b87838ec086625e4e3e2e1e087a6238f938b87821e788e4e3e2e1e08766a0209a97938f8b87821e966a50e260d250807e4e3e2e1e0b584a22250788941e22665e2e4e3e0e187a0a11e247851d80a2347658b189b1497938f8b87811ca2b0884a01f8e328a3070d85838e3e387189b1494a3938f8b87821eb08a3070c3619989423938f8b83861eb26e4e2e3e1e0879d981f93878f8b829688784a19b938f8b87821e807e4e1e3e2e066a5a18c1c963e4e3e2e1e00e0d9ca01f938f8b8780383690ee4e3e2e1e0280da0a018178f938b87809e9e4e3e2e1e00e0d9c38181437938f878b82928078685e3e2e0e4e10da822191a15141f938f8b8782b85e4e3e1e2e0270da03a20a21c9c1814378f938b8782d0e0dc6c5e4e2e1e0e3a4a09c18178f938b87829c6c508074645e4e2e1e0e3ac38201e191a151437938b87838ed060528e3e4e2e1e027a43834a38f938b87809e9280605e3e4e2e1e027a422191a1514381c37938f8b8782d08851834a38f938b87809e928e4e2e1e03498a38f938b84ca66461e08f8214645a08c1f82248e0899186823a0841d8519164282706050de3e4e2e1e0a9231b17938f878b809e90e48864685450d07e4e3e2e1e0b52018178f938b87809e90e070de4e3e1e2e028a43836191a15141f938f8b878122d6087898a8182307a0898e82207a08a1b938f8b878216786e4e185e2e0e39e1b938f8b87821672827c6e4e3e2e1e0c5a51917938b87838e70846e4e1e2e0e345a0a01b938f8b87809f16946e4e3e2e1e04527a11917938f8b87809e8c584a3938f8b87809f1a828c6e4e2e1e034c5a0a31b938f8b84cb16845e0078c1d1782306e4e3e2e1e027c5a31b93878f8b80a316828a7074645e4e3e2e1e0aa1f1624846e4e3e2e1e04527a41d158e824a007891d9b17938f8b878036966c5e4e3e2e1e00da09814a3938f8b87803692e2826c5e4e3e266e1e00daf938b8f878198367072605e4e3e1e2e028a61e9a1517938f8b878036a6685e4e2e3e1e0280da41d989814b837938b8f8782be4e3e2e1e0280d9e358b938f8780a27e085178224745e08c21158b82446e0882117823c0478821178232807260d05e4e3e2e1e0a91b17938b838f84a288747a64645850d08e4e3e2e1e0b58d8782308e0881d18b817938f878b80a2ac626e405e3e2e1e028a517938b8f8780a27470ee4e3e1e2e00da0391c99143423938f878b82ba6e4e3e2e1e0280d else 0x9a15928f025666547e4e3e2e1e048a5211d999793))))
def lay511r11 : Packing := (782,3,5,63,0,16,1,word511r11)
def keys511k12 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xbcb36839000005b3017d35db509405b7654f3040f2306477e23fd8d574ca74d5009d3dad3280193fa5251076a26500002ec474dad02b58faf22d52d9845c914ab1a2a1450247b0936110d0157302e2ff870d8412f20360e3e1fd756cc85b2a8bd86a50d679730000115ee26fa2cf65f5086f96fae07d91eac0d5207f821fc8f0c9a161fea44032c11d4e38739b09129e6ea31239d11bc0790000f0daa841612e1030663bb917906230b6000021deddac72fcd0f600003ed4a16321e9000072f1d12d82bee2ef129d8626a1654cb2e26421260000adfddd3800005ac4c255c546ca7ce8b161a11555a2d3ea7ba071902f956f8032dda84988a09030f250eb12ce3a5ea16042dd4237602e89ce9282b5c96998025cca3a102d821a922c41acacfee060b216b24cf1fbf8ac014ea97aed6b70f5d4e3a95af562209a61f1c57d5003d081e9c350db4251c001d0d2d0dcb2d2204e10fe611aa045f0faf09f1545b58558abc309b0fc62de401440169ea085e2e21142e14997384c105f92b32882997c999df2fbd21b65e1516412d086db50d1b228214bb56bf44901cb7112c82120c142ba0933d9cc78b2757900000000000000000000cde708d7d221f26baa9db1d9811c0000e1970000315be2292d9721b5c03a7166b1e5a907268200006420e027000000004507a11550e10000000000005aab8279a0b700000174b0200804000034a6b42222daf9dbc93e3968c273c9b7e17b01dcea957068664d00cb7ea6e6e33253612afdb5e9e7220fa2783217506ed2dc2dde830c3dfe11f2ceb1096da0fd4187e50481072800050413070c0204020a18040d052f02040500081e040d00003576002c001002080700002400900b000006143d00000627022b07220a0100020e1d2c420206000500730018b40701000200050821020e0805230e1004161a43150009000b111a002b0728061b000700116825120d260600111cb9001f1200cf0b162e730a0400001901000404020803010011022b240c2a000d0a00062b040a1e49461d1900000000500b7f011500000a180366040d0000050000000242004100040901021e00003b4d0916060003000000040000040c000812183d23010000000200126707286216000b58010c02070000197e03000d01022e000200080905110201000000a61c1e154e0028000603650b033f2a0f020200000003000037000b290e1619431d0000093c000016002b004c00250006050d00650300350019000d0003003f8a081b00000b07010b000f0000500003d1002a030000020e0216000008000403000001203d02000a05024a059a2700140f1a0656000013000e015a4c0024040222151a1302000004191311550063620400001303000a7000070e1d010002002e0c0000010f42090b25053d3c004f08191d060159000300000b00e3 else 0x9da941f32a96e01b39d330cc23041294887d303c0000705506470000f2870000000000000000d2f4657a000071c1000011ce0000c0580000f146000070343862700bd2b0e9443d8ef953e0a99a8580ac000000000000604729587274e1ee520541c7100fb30bd0703059f97fcef604a50000595d01d27d9611590000d0f0e18420844402e18131b3855f0000000050ffc27032c7fa638241aec6b41a6ea78860c28f0000515d3cd5f2c010a800000000c2ee0000fe001de3000002bcf803dd6faa1882eb4618e6810000f1e2000012d77b04c9c8000000000000000021e16a932eae917a01edb2dba6e6f689513c32675b010000866f3054967a01a4eae8000012140000221061932219f00c8099ca6e22cdf131ca89853e1111a65a403692181195f5bdd12352f2c170b17670c2e14170ef0000000012498539103bc574615a61a8219f91ad3064206b9aa7e27dd2c4c14240af44f0661ca26c50b1b67d020cd01df0c5041eba8aa24251186ddbd4477290a46374821113c0ec701c52bbc656ca7639c408cb49bf92b2dd25f0b042232ed551c05a989227f097c1dacea9b1bd0021a1cfd86c01cab1ef52b7b0de9dffc0a7469e419c1307e1373db35ab9c98741292289f2c9190cc1d6d5592086a306b59fe25bb13e40c05892c9d8761bf17e40cf7871284b3ccb319a4de82af6d03df16de2d852c28d95f092e12c71e0365fa4d0961086f6a1830260a2152c21605a11c24d8d9df5d99c41ba52830d07906c41fc91f92a7f710080b4062ac57180aacd3956ee681e728dc14f7c22002a65b85269994321495806e65461406853faa4353692400026d178706df07bda1a354ec2fd9049a649c128f21e422e69b1f27635a8022f3ece5ecd24068301d1b431cc75a0509ce29c91a6b0e4b2e3c00ec27c464c0d4f68c936a7f26ed0b265f480c8a6f8bd0574a36b052231063171f732a16252d810724e906f501ed4bda0225a94e0a17541d029713a32a0704db117edc9828b294732504085827fd2acd975f21251db0028bde9625402c622cbda8776c6ec82a0fb30baf14302c5486960d33157f6aae8072154f96590751879e5e3347476ea9ccc016901aed464522261fae1a0a5779119b981e1162a9c02a62ce5a16e0c1151e74da2808bc0dd82b9910ef982430531ffb2afc5fc0061d818105c42a222a901566880a0cdf1d801356877fa6a19c121c680749824953b6296342562b12194524f10129a3860bddafc620e88a9213b62980000043c0000a000d1c99124608c907cee9ea2e04a64608236380000d224b30d0000d035318e2158b04351a5022b5d9f1226f0461078000001d340df227ad5d3a984a11e0000c55e107a016f51f0b0f30000b450f934368796a9345e215f823821c80000c13d859770631a99a9420000) else (if i < 3 then 0x12abab0ba190e0c3561f52bd618810a4a966b077c0a5916b9233656e40ce81b7d1a711204ea230e66aede00822b6353572d1623ae4abb0c6128140113248594b42b464cdf161166de01991d06204785922a352aec2d4814d8941d2e642e9b1cd12a841f4812fe246a0091a8c3657c5b5c1c530a07a6142a54235b23bb286710c821d66e01220a2f9aaf85a529cb46a4ef12be902b1b2c051808721526103a94850bb36a616551a58e8e75df6a0d7613ff97e3999619dc41841347aba1848fe829186719bf578e5de0000f5fe605d96b1981a0207853db039e9d9ec635272d28e4d1e3004b83b0000fda100000000b213f256923c0072000011728eca4162105b0000206af680c17301aa305720d460f4f2e8da5d92df8066b62df2937053418c0000991b3460583a6192bd37029b00004cfcc24d465b00000000f1be41e4803f624300000000d12222f60000c8b4f0416dabb4f72201000000008ab8416a0000541966c10e18965d41afe27b5a97f54dbaca12252ddd2234f9d7c2e2cda51096d30a0000000078709d98c12791679ecb3dc50000c14c126136290000f114f1712105619ef954209eb6350000242eb10891b8304a810200000000c2ad6065ea92b0e90000000000000000d549000000a2c04b0000a067e268610a845bf136269fa284995bd46884550000a1440000b15340b95285965cb513f8a8c51889df1150a1b0008f74d8e083e93792edde9daa72c548d2f82037309100000000d4f40000000020e83088b0b3a1dd821ce2ea6c894258aa3032bfc2b559dd829982f5d196301f29b9c0137850f0d8000091060000a61306e431d53e9b61d152d6007e000098a3f303f2a7710f3a5166ef20c714d2f0f722aa91c4d0ada1bf0000025f10e056cac0b58625a8fc00000000000020b891b60000f2020000f43a70f80000000000005ecca0be54ecc2e42e9530f1000044f874a27245b17c9168b49f31511a54000052a4cc1e3232818f5d1dc24b094060a6e0ea5138496e8441d99bfa86e155c1b1420ac24af11f64cb218014e29101a8615132b85ca979d465695221eca04ce2ec085128751544925d3964908972fec03882b8966e00009297b277cd700000000a90c4da8d04fc0000000041a32042f1d701300000f4750000b65800001a8e026aa86dc8fe98676177903100000000605ec22a896a2b0000009ea18962818a584361250000b909000011e3020dd00230e2108d9a6d00000da300000000b1df90e78200319100000000000072c3d275401a205285dc0000e033896cc9725538d10da121d5c351f5c4cc428a5044000062cc693d000000003963386603000000b8767199ca9034116095c07320f9b0d9d84000002e5470bfc2fa726dc208a09805b626f79a74ce9ff206fe3882f395bc10ca429a70ed325a3198626600000000 else 0x153712ca0d9c6148461260bc0000a4f571f6c03e685aa16c59d49147b0063808b2915405d04800000000917981e8018b22e74905b4d4c8ae000055b955a16a8061f8000074b03024f23e0000c5ab9236b5702414f6887af7c94af056d945ca880000618ddc64b17f61ab3104495f000081b99ec5ea573957a005d0ee943b01c3d11d21ebee8311339aa6b8e5f263f0a3298a0000d5f216327259681770ab72f085e728eff85f00000000c956110bb95154e544ba12d5fab18946001852f7a9772271f65e8308f6d45e9c8025a0d008cae023c29269c9f847c87ac257e2c8e44fb1d4000065fd315c04b27209f27ea00d60c900004050a0e550171486989d20ae69d20000ea842175196b00000000d010000022880000b244960f0000cac5000081a959509069e6abd960809b11397a79c90f3007e25e00004683000000008a9f0000a4a4408ec90ae18991853ccae262428c54fe00008b0c229fc109723d61e65295b02ca1bc31bb4182508aa20b22e5304fb080))
def cut511k11p0 (i : Nat) : Nat := 0x80904
def cut511k11p42 (i : Nat) : Nat := 0x809040000000000080904000000000008090400000000000809040000000000080904000000000000050000000000000009840000000000040884000000000004088400000000000210880000000000021088000000000002108800000000000809040000000000040904
def cut511k11p281 (i : Nat) : Nat := 0x80904000000000008090400000000000809040000000000080904000000000008090400000000000809040000000000040884000000000004088400000000000408840000000000040884000000000004088400000000000408840000000000092190000000000002108800000000000210880000000000021088000000000002108800000000000210880000000000021088000000000002108800000000000210880000000000090500000000000006028000000000000809040000000000040904
def cut511k11p639 (i : Nat) : Nat := 0x222410024282109e222410004282109e224205040921218e48088c0c029281d6812402100414421248088c0c029281d648088c0c029281d648088c0c029281d648088c0c029281d648088c0c029281d642440208082241d2224205040921218e224205040921218e1142200021440862224205040921218e224205040921218e224205040921218e222410004282109e222410004282109e24442002838420e2224205040921218e222410024382109e224205040921218e222410024382109e222410024382109e811201100214220e224205040921218e111040220210854211104022021085421110402202108542111040220210854242084408002a81d61110402202108542111040220210854211104022021085421110402202108542111040220210854220a8040016008416111040220210854211104022021085421110402202108542111040220210854242084408002a81d611104022021085421110402202108542111040220210854211104022021085421110402202108542111040220210854220a804001600841611104022021085421110402202108542111040220210854211104022021085421110402202108542111040220210854220a100840409118a20a100840409118a20a100840409118a20a100840409118a20a100840409118a42084408002a81d620a120840c09118a10c0804208088946
def cut511k11p703 (i : Nat) : Nat := 0x109108001121041a109108001121041a109108001121041a109108001121041a42084408002a81d642084408002a81d6109108101921041a109108101921041a109108001121041a11105022061085421110502206108542a018885003040a061110502206108542111050220610854250190488030211ca111050220610854211105022061085421110702206108542111050220610854220c201040809218e11105022061085421110502206108542109108001121041a109108001121041a20c201040809218e109108001121041a109108001121041a109108001121041a109108001121041a109108081121041a109108101921041aa018885003040a061110402202108542109108001121041a109108001121041a109108101921041a224205040921218e222410004282109e222410004282109e222810004302109e222410004282109e811201100214220e222410004282109e222410024282109e222410004282109e222410004282109e224205040921218e224205040921218e24502008860420e2811211100614220e224205040921218e224205040921218ea018885003040a06222410004282109e222810004302109e222410004282109e222410004282109e222410104282109e222410004282109e222410024282109e222410004282109e222410004282109e222810004302109e222410004282109e
def cut511k11p767 (i : Nat) : Nat := 0x42084408002a81d642084408002a81d6a018885003040a061110602202108542a018885003040a0611106022021085421110602202108542111060220210854242084408002a81d61110402202108542111040220210854242084408002a81d61110602202108542111040220210854220a100840409118a
def word511r12 (i : Nat) : Nat := (if i < 1 then 0xa6c3931e0c51684f931e2c381345a03c64c9f263c587045a84070c17262c3831d218288c98f161c01e9c583261c62260c942880e37263c58705623263c5870079c464c58701498464c78b09299325c98f161c01e84c943a8c9871e2c14a64b931e2c1843d01f261c78b0259c305c583263c21e80f930e3c58044e223458f931e2c38294c94407c98b0e0c74a8c98f161c01e710186a5c98f160c21ea101c70d8d171e4c587056182c68b931e2c3803d41e345c793161c14080c17263c5870501e364c78b0e08b4080e186c5c98f161c15068a37262c787050162e4c78b0e0114088d17263c587050344268a3b263c38b054153068b930e3c58298c1e2e4c78b0e0a04071b93163c38280c1c2e4c78b0e0a0447c98f161c1168109830e0f902e3c5870561f263c5870459f261c78b007982e4c78b0e04d3a64e17263c5870509a2e4c5870639d30551153e4c78b0e0a9345c3931e0c53a78b931e2c381350993c5c98f161c1426c98f161c11670b931e2c3803cf1b263c5870459c6a60b8f262c38284c1c685c98f161c1480000203e4c78b0e09d1882993161c13a0104b263c5867c98f161c12860b931e2c382720182e4c58704e1b263c5844cc908870b8f161c14268b931e2c38278b931e2c3826c99e3f3199887c215ff6f39749b895b36d2d64aafbd676a95513a6752268974149e0cd826532e4948c8de3d71918a643e615b06180e3f5df32f5478ebb45cfce4070136d9ae2d2c67e32a58e4c426092f5171eb5158d2b7154aa6050da79133094547ca2ed0fa83f3f99ed4eee7393769aa0cd462c2f716c0aba52627b12fc90244a1ff0f1c71234b18a0b7454c268111887442e2110ed068c2d8143086035414a0670180003ffd32c37ff65586ffe4ab0dffd8621bffb2a437ff26266fff444cdffd8699bff92b337ffa6575ffecb2ebffc965d7ffb0cbafff21975fff332ebffd861d7ff90c3afff99875fff4cacbffd98597ff930b2fffa2165ffecbacbffc97597ffb0eb2fff61965ffe432cbffd76597ffcccb2fff61565ffebaacbffe88197ffb0e32fff21c65ffec30cbffd76197ffcef2afff61a55ffe434abffd76957ff8ed2afff99a55bff4cb0d7fe9921bdfb0c435ff65486fbeca90dfdd9321bff320437bf66266f7e4c4cdefd9599bdf92b335ff66266bfe4c4cdbfe8899bdfb0d337bf21a66bfecaccd7fe995d6ff92cbafbf99975bfecb0ebefe661d6ffd32b2dff66165bfe4c2cbbfe88596ffb2eb2fbf5d965f7f332cbf7d85596ffb3032effa2065bfecb8cbefe66197efaca32fdf25e55fbe4b4abf7d86957ef90d2afdf5da55fbe3b4abf7e66957bfcef2adff25a55f7f334abf7d75957efacb2aebf61886ebeba8ebe7d65196efb2a435f764c86bfcc810dafe8899adfb2c3adf764c75bfcc80eb7bd94197afcef2af9f99a55 else 0x4c94407c98b0e0c74a64b93161c18e7c98b0e0c69664c94464c5870630f4a64a23263c587007a532551930e3c5803d2223268a943a88f931e2c382d8c9a2a511930e2c18c3d7930e3c5812879c305c98f161c0386d23b263c58700d9e3451c9c6e3c98b0e0a87080e36345c98b0e0c758e0e354468a9f1e4c587058386878d153e3c98b0e0ae364c5870638b3a84f1b263c587045a43a78d931e2c3822d21c2e4c78b0e01b426c98b1e1c03670e982c55037263c5870561e3260a3444551931e2c382d4d931e2c3806ce1628dc98f161c09a9101c70d4d171e2c393056223261a143c5c987163c160d8d15464c78b0e00f50e1a182874d17261c78b05919345c9871e2c01e9101e3260b931e2c3806d61c3054d931e2c3806d4213288f931e2c3822d439347c18f161c9169511f263c5870268b4a60f93161c18e2d039307c3931e0c5169c98f161c09a2ce203c64d93161c18e2d41e326509f263c587045ac3)
def lay511r12 : Packing := (102,2,5,63,0,13,1,word511r12)
def keys511k13 (i : Nat) : Nat := 0x68ec0004130005b4301400000000030b600049f000000064a70c68ded53048a4e298b38b34099fc094120a462819d8c8bf258216496485a005d61bcca41ac2832880d6299a34c115135a1fc163899968ac811250ba0ca297161f2e8f0f28e24e0007671448b1f21fb15888190956db4c7c9201bf07e07556b233e0ab15481c20c40f7f2d50760049a8ab0c4c2ad620f065550a3ea2e70180019a2e5ed24e0a6511f2811978059b5d1c00004284207047a15e35fccd6630eb5967c75a10001035010213b90c001c8f42f4827629057a510b1c000d2ba4074900004a6315e31800000041080014068dab9e8ab94a513cc5f601e884839b14bd24c88f8346f071acc109411e435f862938d094574a2d54328afc00d724a719bb43991b02f52a0000c39aa100000b850e0000000915c7bc97ee8208e4c7c1f083892c57800421560c04994640000000000a47427ea4bc2340156a0987c16f8700058d859c00341063800b0010403810410c8084480201024f84182000c3a28104280c080063c28a06301000000080020c1110800b010208699
def cut511k12p10 (i : Nat) : Nat := 0x8090400000000000408840000000000021088
def word511r13 (i : Nat) : Nat := 0x61648a18239c61481e48e2860a461479238a18281858e48a18271a48e28601671859238a18271e48e28601671a48e28601679238a18251648e28609b61749f439bcae3f1385400ffd86ffc86ffe66ffd75ffc75ffd65ffc65ffe55efe66f7e55
def lay511r13 : Packing := (10,1,5,63,0,9,1,word511r13)
def keys511k14 (i : Nat) : Nat := 0x180ccf62f24000030200000a040000000000007d000000000000000000000000000058c000014500000d100000207001d1001930000000397002e0000000000000243e20000000000000550000028659000000000000000000000000000100
def word511r14 (i : Nat) : Nat := 0x20c4104bff
def lay511r14 : Packing := (1,0,5,63,0,0,1,word511r14)
def samp511 : Array (Bits × Bits) := #[(0x44accc02400000dd5596002cb00198000090f05140056656600333300002035249f520024007ffe739ce739c007ff,0x44accc026908004d559748acba459d22009050516a0d6656750b333a8400015248b5350a6a1350e318c6318ea1543),((~~~(0x7fcff0f77ffffed999e7ffcf3ffe0000b31d3f9e7ff987987ffc3c3ffff3f2638e663ffc7ff9ffc6318c6318007ff : Bits)),(~~~(0x7fcffaf77cb7fff999e7e54f3f2b5794b31d3f9e79b187987cd43c3e6bfbfa638e663cb47969cb56b5ad6b5b9672d : Bits))),(0x800f043000599c787e0003f0001e00000030a82000780780003ffffff3131e07e1e0003fff8003e0f83e0f800000,0x8005043181d99c787e0c1bf060de30600000a82182f80780c1955560f1111e05a1e0c1ad838c1be0f83e0f98530a),(0x3f000000061e07f800003ffffe000000fc0cfc0007ff800003fc0001c1c1ff801ffffc0000003ff003ff0000000,0x350000011e0a07f80009b5d04e002600b40cfc022fff80011bfc008d4141f6801f611c023011bff003ff002504a),(0xc0008c0007e007ffffffc0000000008f000f000007fffffffc000001fe01ffffe000000000003ffffc000000000,0x8c00dea007feba07c0003c001e85000f0000efaafaa07c00003dfe01ffffe000d801b00dbffffc00001d03a),(0xf0000f00007fff80000000000000000f0000ffffff800000000000001fffe00000000000000003ffffffffffffff,0x90000f01097ffb0000085000428021490000f8610b000000850000429fbfa000000089011208914a5294a511622c),((~~~(0xfffff000007ffffffffffffffffffff00000ffffffffffffffffffffe000000000000000000003ffffffffffffff : Bits)),(~~~(0x6fffff637d1fffffffffe9ffff4fffa700b45ffffb3ffffffd9ffffecf5151f6dabf7d1efa3bd1ffffffffffa7f4f : Bits))),((~~~(0xffffffffffffffffffffffffff00000000000000000000000001fffffffffffffffffffffffffffffffffff : Bits)),(~~~(0x90050ffdcfffffffffee7fff73ffb9f95000f8618ffaafaac7d55563fffffffffffecffd9fecffffffffffd9fb3f : Bits))),((~~~(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff : Bits)),0x6fcafa637c0155f80145e00a2f01578000000000380000001c00000e0000000000001c003801c0000000000380700)]
def cols511 : IndexTree ColumnInfo := (.fork 13 (.fork 6 (.fork 3 (.leaf [(1,0,510,0,13),(2,0,509,0,13),(4,0,507,0,13)]) (.leaf [(8,0,503,0,13),(16,0,495,0,13),(32,0,479,0,11)])) (.fork 3 (.leaf [(128,0,383,0,11),(64,0,447,0,10),(256,0,255,0,10)]) (.leaf [(33,0,478,0,10),(34,0,477,0,10),(132,0,379,0,10),(144,0,367,0,10)]))) (.fork 7 (.fork 3 (.leaf [(0,32,348,131,9),(0,128,331,52,9),(36,0,475,0,9)]) (.leaf [(40,0,471,0,9),(48,0,463,0,9),(65,0,446,0,9),(68,0,443,0,9)])) (.fork 3 (.leaf [(72,0,439,0,9),(129,0,382,0,9),(130,0,381,0,9)]) (.leaf [(136,0,375,0,9),(258,0,253,0,9),(264,0,247,0,9),(272,0,239,0,9)]))))
def lv511 : Nat → Packing
  | 8 => lay511r8
  | 9 => lay511r9
  | 10 => lay511r10
  | 11 => lay511r11
  | 12 => lay511r12
  | 13 => lay511r13
  | 14 => lay511r14
  | _ => emptyPacking
def ix511 : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 31 110 5 13 7 2 keys511k9
  | 10 => lookupWord 486 1651 8 17 11 2 keys511k10
  | 11 => lookupWord 987 3350 8 17 11 2 keys511k11
  | 12 => lookupWord 442 1501 8 16 10 2 keys511k12
  | 13 => lookupWord 62 213 7 13 7 2 keys511k13
  | 14 => lookupWord 6 74 3 10 4 2 keys511k14
  | _ => fun _ => none
def g511 : Forest := ⟨511,14,fun j => samp511[j]?.getD (0,0),cols511,#[[],[16,66,134],[32,65,117],[64,33,117,134]],lv511,ix511,noFactory,noFactorySound 511⟩
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm328 : graphValid g328 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck328k3p0 : mixedBlock g328 3 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all328k3 : mixedBlock g328 3 0 1 := ck328k3p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok328 : mixedTables g328 3 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g328 0 0)
  · exact (mixedEmpty g328 1 0)
  · exact (mixedEmpty g328 2 0)
  · exact all328k3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low328 : Lower (vars 328) (graphGoal 328) 4 :=
  mixedLower (g:=g328) (i:=0) (hints:=12935258112) (before_sound [] baseKnown) gm328 ok328 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp328 : List (Nat × List Nat) := [(328,[])]
def kn328 := extendKnown [] 4 mp328
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl328 : Known kn328 := extendKnown_ok baseKnown low328 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm99 : graphValid g99 (boundsBefore kn328) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck99k3p0 : mixedBlock g99 3 0 1 := by
  apply mixedCut (data:=cut99k3p0)
  decide +kernel
theorem all99k3 : mixedBlock g99 3 0 1 := ck99k3p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok99 : mixedTables g99 3 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g99 0 0)
  · exact (mixedEmpty g99 1 0)
  · exact (mixedEmpty g99 2 0)
  · exact all99k3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low99 : Lower (vars 99) (graphGoal 99) 4 :=
  mixedLower (g:=g99) (i:=0) (hints:=85) (before_sound kn328 vl328) gm99 ok99 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp99 : List (Nat × List Nat) := [(99,[]),(101,[101,33]),(105,[101,49,33]),(165,[112,96,32,16]),(166,[112,96,32]),(178,[112,96,64,48,32]),(197,[101,117,32,16]),(204,[101,117,49,32]),(225,[113,65,49,33]),(228,[81,113,65,49,32]),(291,[134,118,16]),(298,[133,117,101,49,16,32]),(323,[128,80,117,96,16]),(326,[133,117,96,32]),(340,[128,80,117,96,64,16,49,32]),(353,[129,101,113,65,49,33]),(354,[133,81,101,113,65,49,16,32]),(418,[134,113,65,49,16,32]),(452,[97,101,133,113,65,49,32])]
def kn99 := extendKnown kn328 4 mp99
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl99 : Known kn99 := extendKnown_ok vl328 low99 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm329 : graphValid g329 (boundsBefore kn99) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck329k4p0 : mixedBlock g329 4 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all329k4 : mixedBlock g329 4 0 1 := ck329k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok329 : mixedTables g329 4 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g329 0 0)
  · exact (mixedEmpty g329 1 0)
  · exact (mixedEmpty g329 2 0)
  · exact (mixedEmpty g329 3 0)
  · exact all329k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low329 : Lower (vars 329) (graphGoal 329) 5 :=
  mixedLower (g:=g329) (i:=0) (hints:=12884926470) (before_sound kn99 vl99) gm329 ok329 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp329 : List (Nat × List Nat) := [(329,[]),(330,[134,16]),(332,[32,16])]
def kn329 := extendKnown kn99 5 mp329
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl329 : Known kn329 := extendKnown_ok vl99 low329 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm488 : graphValid g488 (boundsBefore kn329) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck488k5p0 : mixedBlock g488 5 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all488k5 : mixedBlock g488 5 0 1 := ck488k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok488 : mixedTables g488 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g488 0 0)
  · exact (mixedEmpty g488 1 0)
  · exact (mixedEmpty g488 2 0)
  · exact (mixedEmpty g488 3 0)
  · exact (mixedEmpty g488 4 0)
  · exact all488k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low488 : Lower (vars 488) (graphGoal 488) 6 :=
  mixedLower (g:=g488) (i:=0) (hints:=14284775424) (before_sound kn329 vl329) gm488 ok488 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp488 : List (Nat × List Nat) := [(488,[])]
def kn488 := extendKnown kn329 6 mp488
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl488 : Known kn488 := extendKnown_ok vl329 low488 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm103 : graphValid g103 (boundsBefore kn488) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck103k4p0 : mixedBlock g103 4 0 1 := by
  apply mixedCut (data:=cut103k4p0)
  decide +kernel
theorem all103k4 : mixedBlock g103 4 0 1 := ck103k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok103 : mixedTables g103 4 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g103 0 0)
  · exact (mixedEmpty g103 1 0)
  · exact (mixedEmpty g103 2 0)
  · exact (mixedEmpty g103 3 0)
  · exact all103k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low103 : Lower (vars 103) (graphGoal 103) 5 :=
  mixedLower (g:=g103) (i:=0) (hints:=1621) (before_sound kn488 vl488) gm103 ok103 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp103 : List (Nat × List Nat) := [(103,[]),(107,[50]),(230,[112,64,98,48]),(236,[101,82,114,33,32,65,48]),(241,[97,113,66,49,80]),(299,[134,118,50,16]),(406,[101,134,117,64,48]),(422,[97,134,16,112,64,81,48]),(454,[32,133,112,64,98,48]),(481,[130,113,66,49]),(484,[82,81,129,114,32,65,48])]
def kn103 := extendKnown kn488 5 mp103
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl103 : Known kn103 := extendKnown_ok vl488 low103 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm109 : graphValid g109 (boundsBefore kn103) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck109k4p0 : mixedBlock g109 4 0 1 := by
  apply mixedCut (data:=cut109k4p0)
  decide +kernel
theorem all109k4 : mixedBlock g109 4 0 1 := ck109k4p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok109 : mixedTables g109 4 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g109 0 0)
  · exact (mixedEmpty g109 1 0)
  · exact (mixedEmpty g109 2 0)
  · exact (mixedEmpty g109 3 0)
  · exact all109k4
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low109 : Lower (vars 109) (graphGoal 109) 5 :=
  mixedLower (g:=g109) (i:=0) (hints:=26117) (before_sound kn103 vl103) gm109 ok109 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp109 : List (Nat × List Nat) := [(167,[112,96,80,49,32]),(205,[117,32]),(357,[131,115,67]),(453,[83,133,115,67,32])]
def kn109 := extendKnown kn103 5 mp109
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl109 : Known kn109 := extendKnown_ok vl103 low109 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm229 : graphValid g229 (boundsBefore kn109) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck229k5p0 : mixedBlock g229 5 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck229k5p1 : mixedBlock g229 5 1 2 := by
  apply mixedCut (data:=cut229k5p1)
  decide +kernel
theorem all229k5 : mixedBlock g229 5 0 3 := (@mixedJoin g229 5 0 1 2 ck229k5p0 ck229k5p1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck229k6p0 : mixedBlock g229 6 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all229k6 : mixedBlock g229 6 0 1 := ck229k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok229 : mixedTables g229 6 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g229 0 0)
  · exact (mixedEmpty g229 1 0)
  · exact (mixedEmpty g229 2 0)
  · exact (mixedEmpty g229 3 0)
  · exact (mixedEmpty g229 4 0)
  · exact all229k5
  · exact all229k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low229 : Lower (vars 229) (graphGoal 229) 7 :=
  mixedLower (g:=g229) (i:=0) (hints:=536872453) (before_sound kn109 vl109) gm229 ok229 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp229 : List (Nat × List Nat) := [(229,[]),(355,[135,101,33])]
def kn229 := extendKnown kn109 7 mp229
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl229 : Known kn229 := extendKnown_ok vl109 low229 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm361 : graphValid g361 (boundsBefore kn229) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck361k5p0 : mixedBlock g361 5 0 2 := by
  apply mixedVerified
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck361k5p2 : mixedBlock g361 5 2 3 := by
  apply mixedCut (data:=cut361k5p2)
  decide +kernel
theorem all361k5 : mixedBlock g361 5 0 5 := (@mixedJoin g361 5 0 2 3 ck361k5p0 ck361k5p2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck361k6p0 : mixedBlock g361 6 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all361k6 : mixedBlock g361 6 0 1 := ck361k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok361 : mixedTables g361 6 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g361 0 0)
  · exact (mixedEmpty g361 1 0)
  · exact (mixedEmpty g361 2 0)
  · exact (mixedEmpty g361 3 0)
  · exact (mixedEmpty g361 4 0)
  · exact all361k5
  · exact all361k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low361 : Lower (vars 361) (graphGoal 361) 7 :=
  mixedLower (g:=g361) (i:=0) (hints:=12884926469) (before_sound kn229 vl229) gm361 ok361 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp361 : List (Nat × List Nat) := [(361,[]),(362,[134,16]),(460,[117,32,16])]
def kn361 := extendKnown kn229 7 mp361
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl361 : Known kn361 := extendKnown_ok vl229 low361 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm331 : graphValid g331 (boundsBefore kn361) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck331k5p0 : mixedBlock g331 5 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all331k5 : mixedBlock g331 5 0 1 := ck331k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok331 : mixedTables g331 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g331 0 0)
  · exact (mixedEmpty g331 1 0)
  · exact (mixedEmpty g331 2 0)
  · exact (mixedEmpty g331 3 0)
  · exact (mixedEmpty g331 4 0)
  · exact all331k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low331 : Lower (vars 331) (graphGoal 331) 6 :=
  mixedLower (g:=g331) (i:=0) (hints:=4294992006) (before_sound kn361 vl361) gm331 ok331 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp331 : List (Nat × List Nat) := [(331,[]),(334,[134,16,32]),(348,[65,32])]
def kn331 := extendKnown kn361 6 mp331
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl331 : Known kn331 := extendKnown_ok vl361 low331 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm333 : graphValid g333 (boundsBefore kn331) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck333k5p0 : mixedBlock g333 5 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all333k5 : mixedBlock g333 5 0 1 := ck333k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok333 : mixedTables g333 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g333 0 0)
  · exact (mixedEmpty g333 1 0)
  · exact (mixedEmpty g333 2 0)
  · exact (mixedEmpty g333 3 0)
  · exact (mixedEmpty g333 4 0)
  · exact all333k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low333 : Lower (vars 333) (graphGoal 333) 6 :=
  mixedLower (g:=g333) (i:=0) (hints:=12884928006) (before_sound kn331 vl331) gm333 ok333 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp333 : List (Nat × List Nat) := [(333,[])]
def kn333 := extendKnown kn331 6 mp333
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl333 : Known kn333 := extendKnown_ok vl331 low333 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm250 : graphValid g250 (boundsBefore kn333) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck250k5p0 : mixedBlock g250 5 0 1 := by
  apply mixedCut (data:=cut250k5p0)
  decide +kernel
theorem all250k5 : mixedBlock g250 5 0 1 := ck250k5p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok250 : mixedTables g250 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g250 0 0)
  · exact (mixedEmpty g250 1 0)
  · exact (mixedEmpty g250 2 0)
  · exact (mixedEmpty g250 3 0)
  · exact (mixedEmpty g250 4 0)
  · exact all250k5
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low250 : Lower (vars 250) (graphGoal 250) 6 :=
  mixedLower (g:=g250) (i:=0) (hints:=1125605456) (before_sound kn333 vl333) gm250 ok250 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp250 : List (Nat × List Nat) := [(429,[134,66,16])]
def kn250 := extendKnown kn333 6 mp250
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl250 : Known kn250 := extendKnown_ok vl333 low250 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm238 : graphValid g238 (boundsBefore kn250) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck238k6p0 : mixedBlock g238 6 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all238k6 : mixedBlock g238 6 0 1 := ck238k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok238 : mixedTables g238 6 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g238 0 0)
  · exact (mixedEmpty g238 1 0)
  · exact (mixedEmpty g238 2 0)
  · exact (mixedEmpty g238 3 0)
  · exact (mixedEmpty g238 4 0)
  · exact (mixedEmpty g238 5 0)
  · exact all238k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low238 : Lower (vars 238) (graphGoal 238) 7 :=
  mixedLower (g:=g238) (i:=0) (hints:=571500112) (before_sound kn250 vl250) gm238 ok238 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp238 : List (Nat × List Nat) := [(238,[]),(249,[117,65,16,32]),(430,[134,117,33])]
def kn238 := extendKnown kn250 7 mp238
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl238 : Known kn238 := extendKnown_ok vl250 low238 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm243 : graphValid g243 (boundsBefore kn238) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck243k6p0 : mixedBlock g243 6 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all243k6 : mixedBlock g243 6 0 1 := ck243k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok243 : mixedTables g243 6 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g243 0 0)
  · exact (mixedEmpty g243 1 0)
  · exact (mixedEmpty g243 2 0)
  · exact (mixedEmpty g243 3 0)
  · exact (mixedEmpty g243 4 0)
  · exact (mixedEmpty g243 5 0)
  · exact all243k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low243 : Lower (vars 243) (graphGoal 243) 7 :=
  mixedLower (g:=g243) (i:=0) (hints:=1074200661) (before_sound kn238 vl238) gm243 ok243 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp243 : List (Nat × List Nat) := [(373,[135,101,33]),(423,[134,50,66,16]),(437,[134,117,33,64]),(455,[118,101,133,50,32,64,16])]
def kn243 := extendKnown kn238 7 mp243
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl243 : Known kn243 := extendKnown_ok vl238 low243 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm486 : graphValid g486 (boundsBefore kn243) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck486k6p0 : mixedBlock g486 6 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck486k6p1 : mixedBlock g486 6 1 2 := by
  apply mixedCut (data:=cut486k6p1)
  decide +kernel
theorem all486k6 : mixedBlock g486 6 0 3 := (@mixedJoin g486 6 0 1 2 ck486k6p0 ck486k6p1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck486k7p0 : mixedBlock g486 7 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all486k7 : mixedBlock g486 7 0 1 := ck486k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok486 : mixedTables g486 7 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g486 0 0)
  · exact (mixedEmpty g486 1 0)
  · exact (mixedEmpty g486 2 0)
  · exact (mixedEmpty g486 3 0)
  · exact (mixedEmpty g486 4 0)
  · exact (mixedEmpty g486 5 0)
  · exact all486k6
  · exact all486k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low486 : Lower (vars 486) (graphGoal 486) 8 :=
  mixedLower (g:=g486) (i:=0) (hints:=4866442832) (before_sound kn243 vl243) gm486 ok486 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp486 : List (Nat × List Nat) := [(486,[])]
def kn486 := extendKnown kn243 8 mp486
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl486 : Known kn486 := extendKnown_ok vl243 low486 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm489 : graphValid g489 (boundsBefore kn486) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck489k7p0 : mixedBlock g489 7 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all489k7 : mixedBlock g489 7 0 1 := ck489k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok489 : mixedTables g489 7 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g489 0 0)
  · exact (mixedEmpty g489 1 0)
  · exact (mixedEmpty g489 2 0)
  · exact (mixedEmpty g489 3 0)
  · exact (mixedEmpty g489 4 0)
  · exact (mixedEmpty g489 5 0)
  · exact (mixedEmpty g489 6 0)
  · exact all489k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low489 : Lower (vars 489) (graphGoal 489) 8 :=
  mixedLower (g:=g489) (i:=0) (hints:=14227103749) (before_sound kn486 vl486) gm489 ok489 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp489 : List (Nat × List Nat) := [(489,[]),(490,[134,16]),(492,[117,32,16])]
def kn489 := extendKnown kn486 8 mp489
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl489 : Known kn489 := extendKnown_ok vl486 low489 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm366 : graphValid g366 (boundsBefore kn489) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck366k7p0 : mixedBlock g366 7 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all366k7 : mixedBlock g366 7 0 1 := ck366k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok366 : mixedTables g366 7 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g366 0 0)
  · exact (mixedEmpty g366 1 0)
  · exact (mixedEmpty g366 2 0)
  · exact (mixedEmpty g366 3 0)
  · exact (mixedEmpty g366 4 0)
  · exact (mixedEmpty g366 5 0)
  · exact (mixedEmpty g366 6 0)
  · exact all366k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low366 : Lower (vars 366) (graphGoal 366) 8 :=
  mixedLower (g:=g366) (i:=0) (hints:=4329596496) (before_sound kn489 vl489) gm366 ok366 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp366 : List (Nat × List Nat) := [(366,[]),(377,[134,66,16]),(462,[134,117,33])]
def kn366 := extendKnown kn489 8 mp366
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl366 : Known kn366 := extendKnown_ok vl489 low366 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm365 : graphValid g365 (boundsBefore kn366) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck365k7p0 : mixedBlock g365 7 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all365k7 : mixedBlock g365 7 0 1 := ck365k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok365 : mixedTables g365 7 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g365 0 0)
  · exact (mixedEmpty g365 1 0)
  · exact (mixedEmpty g365 2 0)
  · exact (mixedEmpty g365 3 0)
  · exact (mixedEmpty g365 4 0)
  · exact (mixedEmpty g365 5 0)
  · exact (mixedEmpty g365 6 0)
  · exact all365k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low365 : Lower (vars 365) (graphGoal 365) 8 :=
  mixedLower (g:=g365) (i:=0) (hints:=12884928005) (before_sound kn366 vl366) gm365 ok365 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp365 : List (Nat × List Nat) := [(365,[]),(461,[117,32])]
def kn365 := extendKnown kn366 8 mp365
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl365 : Known kn365 := extendKnown_ok vl366 low365 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm335 : graphValid g335 (boundsBefore kn365) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck335k6p0 : mixedBlock g335 6 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all335k6 : mixedBlock g335 6 0 1 := ck335k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok335 : mixedTables g335 6 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g335 0 0)
  · exact (mixedEmpty g335 1 0)
  · exact (mixedEmpty g335 2 0)
  · exact (mixedEmpty g335 3 0)
  · exact (mixedEmpty g335 4 0)
  · exact (mixedEmpty g335 5 0)
  · exact all335k6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low335 : Lower (vars 335) (graphGoal 335) 7 :=
  mixedLower (g:=g335) (i:=0) (hints:=4294993542) (before_sound kn365 vl365) gm335 ok335 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp335 : List (Nat × List Nat) := [(335,[])]
def kn335 := extendKnown kn365 7 mp335
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl335 : Known kn335 := extendKnown_ok vl365 low335 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm231 : graphValid g231 (boundsBefore kn335) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck231k7p0 : mixedBlock g231 7 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all231k7 : mixedBlock g231 7 0 1 := ck231k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok231 : mixedTables g231 7 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g231 0 0)
  · exact (mixedEmpty g231 1 0)
  · exact (mixedEmpty g231 2 0)
  · exact (mixedEmpty g231 3 0)
  · exact (mixedEmpty g231 4 0)
  · exact (mixedEmpty g231 5 0)
  · exact (mixedEmpty g231 6 0)
  · exact all231k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low231 : Lower (vars 231) (graphGoal 231) 8 :=
  mixedLower (g:=g231) (i:=0) (hints:=536872533) (before_sound kn335 vl335) gm231 ok231 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp231 : List (Nat × List Nat) := [(231,[]),(237,[101,114,49]),(245,[117,65,49,32]),(359,[135,101,33]),(435,[134,66,50,16]),(438,[134,117,64,33,48]),(470,[118,133,64,48]),(483,[130,66,50,113]),(485,[101,129,65,114,49])]
def kn231 := extendKnown kn335 8 mp231
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl231 : Known kn231 := extendKnown_ok vl335 low231 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm363 : graphValid g363 (boundsBefore kn231) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck363k6p0 : mixedBlock g363 6 0 4 := by
  apply mixedVerified
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck363k6p4 : mixedBlock g363 6 4 1 := by
  apply mixedCut (data:=cut363k6p4)
  decide +kernel
theorem all363k6 : mixedBlock g363 6 0 5 := (@mixedJoin g363 6 0 4 1 ck363k6p0 ck363k6p4)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck363k7p0 : mixedBlock g363 7 0 2 := by
  apply mixedVerified
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck363k7p2 : mixedBlock g363 7 2 3 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all363k7 : mixedBlock g363 7 0 5 := (@mixedJoin g363 7 0 2 3 ck363k7p0 ck363k7p2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck363k8p0 : mixedBlock g363 8 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all363k8 : mixedBlock g363 8 0 1 := ck363k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok363 : mixedTables g363 8 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g363 0 0)
  · exact (mixedEmpty g363 1 0)
  · exact (mixedEmpty g363 2 0)
  · exact (mixedEmpty g363 3 0)
  · exact (mixedEmpty g363 4 0)
  · exact (mixedEmpty g363 5 0)
  · exact all363k6
  · exact all363k7
  · exact all363k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low363 : Lower (vars 363) (graphGoal 363) 9 :=
  mixedLower (g:=g363) (i:=0) (hints:=4294991957) (before_sound kn231 vl231) gm363 ok363 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp363 : List (Nat × List Nat) := [(363,[])]
def kn363 := extendKnown kn231 9 mp363
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl363 : Known kn363 := extendKnown_ok vl231 low363 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm251 : graphValid g251 (boundsBefore kn363) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck251k7p0 : mixedBlock g251 7 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all251k7 : mixedBlock g251 7 0 1 := ck251k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok251 : mixedTables g251 7 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g251 0 0)
  · exact (mixedEmpty g251 1 0)
  · exact (mixedEmpty g251 2 0)
  · exact (mixedEmpty g251 3 0)
  · exact (mixedEmpty g251 4 0)
  · exact (mixedEmpty g251 5 0)
  · exact (mixedEmpty g251 6 0)
  · exact all251k7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower (vars 251) (graphGoal 251) 8 :=
  mixedLower (g:=g251) (i:=0) (hints:=1074225237) (before_sound kn363 vl363) gm251 ok251 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp251 : List (Nat × List Nat) := [(431,[134,66,16])]
def kn251 := extendKnown kn363 8 mp251
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl251 : Known kn251 := extendKnown_ok vl363 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm381 : graphValid g381 (boundsBefore kn251) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck381k8p0 : mixedBlock g381 8 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all381k8 : mixedBlock g381 8 0 1 := ck381k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok381 : mixedTables g381 8 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g381 0 0)
  · exact (mixedEmpty g381 1 0)
  · exact (mixedEmpty g381 2 0)
  · exact (mixedEmpty g381 3 0)
  · exact (mixedEmpty g381 4 0)
  · exact (mixedEmpty g381 5 0)
  · exact (mixedEmpty g381 6 0)
  · exact (mixedEmpty g381 7 0)
  · exact all381k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low381 : Lower (vars 381) (graphGoal 381) 9 :=
  mixedLower (g:=g381) (i:=0) (hints:=12885452293) (before_sound kn251 vl251) gm381 ok381 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp381 : List (Nat × List Nat) := [(381,[]),(382,[134,66,16]),(463,[117,65,32]),(475,[134,117,33,64])]
def kn381 := extendKnown kn251 9 mp381
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl381 : Known kn381 := extendKnown_ok vl251 low381 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm247 : graphValid g247 (boundsBefore kn381) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck247k8p0 : mixedBlock g247 8 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all247k8 : mixedBlock g247 8 0 1 := ck247k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok247 : mixedTables g247 8 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g247 0 0)
  · exact (mixedEmpty g247 1 0)
  · exact (mixedEmpty g247 2 0)
  · exact (mixedEmpty g247 3 0)
  · exact (mixedEmpty g247 4 0)
  · exact (mixedEmpty g247 5 0)
  · exact (mixedEmpty g247 6 0)
  · exact (mixedEmpty g247 7 0)
  · exact all247k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low247 : Lower (vars 247) (graphGoal 247) 9 :=
  mixedLower (g:=g247) (i:=0) (hints:=537331285) (before_sound kn381 vl381) gm247 ok247 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp247 : List (Nat × List Nat) := [(247,[]),(375,[135,101,33]),(439,[134,66,16]),(471,[118,101,133,32,64,16])]
def kn247 := extendKnown kn381 9 mp247
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl247 : Known kn247 := extendKnown_ok vl381 low247 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm239 : graphValid g239 (boundsBefore kn247) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck239k8p0 : mixedBlock g239 8 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all239k8 : mixedBlock g239 8 0 1 := ck239k8p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok239 : mixedTables g239 8 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g239 0 0)
  · exact (mixedEmpty g239 1 0)
  · exact (mixedEmpty g239 2 0)
  · exact (mixedEmpty g239 3 0)
  · exact (mixedEmpty g239 4 0)
  · exact (mixedEmpty g239 5 0)
  · exact (mixedEmpty g239 6 0)
  · exact (mixedEmpty g239 7 0)
  · exact all239k8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low239 : Lower (vars 239) (graphGoal 239) 9 :=
  mixedLower (g:=g239) (i:=0) (hints:=536897109) (before_sound kn247 vl247) gm239 ok239 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp239 : List (Nat × List Nat) := [(239,[]),(253,[117,65,32]),(443,[134,66,16]),(446,[134,117,33,64])]
def kn239 := extendKnown kn247 9 mp239
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl239 : Known kn239 := extendKnown_ok vl247 low239 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm494 : graphValid g494 (boundsBefore kn239) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck494k6p0 : mixedBlock g494 6 0 3 := by
  apply mixedCut (data:=cut494k6p0)
  decide +kernel
theorem all494k6 : mixedBlock g494 6 0 3 := ck494k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck494k7p0 : mixedBlock g494 7 0 1 := by
  apply mixedCut (data:=cut494k7p0)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck494k7p1 : mixedBlock g494 7 1 26 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck494k7p27 : mixedBlock g494 7 27 6 := by
  apply mixedCut (data:=cut494k7p27)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck494k7p33 : mixedBlock g494 7 33 9 := by
  apply mixedCut (data:=cut494k7p33)
  decide +kernel
theorem all494k7 : mixedBlock g494 7 0 42 := (@mixedJoin g494 7 0 33 9 (@mixedJoin g494 7 0 27 6 (@mixedJoin g494 7 0 1 26 ck494k7p0 ck494k7p1) ck494k7p27) ck494k7p33)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck494k8p0 : mixedBlock g494 8 0 14 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck494k8p14 : mixedBlock g494 8 14 1 := by
  apply mixedCut (data:=cut494k8p14)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck494k8p15 : mixedBlock g494 8 15 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck494k8p79 : mixedBlock g494 8 79 10 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck494k8p89 : mixedBlock g494 8 89 38 := by
  apply mixedCut (data:=cut494k8p89)
  decide +kernel
theorem all494k8 : mixedBlock g494 8 0 127 := (@mixedJoin g494 8 0 89 38 (@mixedJoin g494 8 0 79 10 (@mixedJoin g494 8 0 15 64 (@mixedJoin g494 8 0 14 1 ck494k8p0 ck494k8p14) ck494k8p15) ck494k8p79) ck494k8p89)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck494k9p0 : mixedBlock g494 9 0 4 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck494k9p4 : mixedBlock g494 9 4 13 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all494k9 : mixedBlock g494 9 0 17 := (@mixedJoin g494 9 0 4 13 ck494k9p0 ck494k9p4)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck494k10p0 : mixedBlock g494 10 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all494k10 : mixedBlock g494 10 0 1 := ck494k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok494 : mixedTables g494 10 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g494 0 0)
  · exact (mixedEmpty g494 1 0)
  · exact (mixedEmpty g494 2 0)
  · exact (mixedEmpty g494 3 0)
  · exact (mixedEmpty g494 4 0)
  · exact (mixedEmpty g494 5 0)
  · exact all494k6
  · exact all494k7
  · exact all494k8
  · exact all494k9
  · exact all494k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low494 : Lower (vars 494) (graphGoal 494) 11 :=
  mixedLower (g:=g494) (i:=0) (hints:=4866467408) (before_sound kn239 vl239) gm494 ok494 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp494 : List (Nat × List Nat) := [(494,[])]
def kn494 := extendKnown kn239 11 mp494
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl494 : Known kn494 := extendKnown_ok vl239 low494 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm493 : graphValid g493 (boundsBefore kn494) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck493k6p0 : mixedBlock g493 6 0 1 := by
  apply mixedCut (data:=cut493k6p0)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck493k6p1 : mixedBlock g493 6 1 2 := by
  apply mixedCut (data:=cut493k6p1)
  decide +kernel
theorem all493k6 : mixedBlock g493 6 0 3 := (@mixedJoin g493 6 0 1 2 ck493k6p0 ck493k6p1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck493k7p0 : mixedBlock g493 7 0 11 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck493k7p11 : mixedBlock g493 7 11 1 := by
  apply mixedCut (data:=cut493k7p11)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck493k7p12 : mixedBlock g493 7 12 8 := by
  apply mixedCut (data:=cut493k7p12)
  decide +kernel
theorem all493k7 : mixedBlock g493 7 0 20 := (@mixedJoin g493 7 0 12 8 (@mixedJoin g493 7 0 11 1 ck493k7p0 ck493k7p11) ck493k7p12)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck493k8p0 : mixedBlock g493 8 0 8 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck493k8p8 : mixedBlock g493 8 8 40 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck493k8p48 : mixedBlock g493 8 48 15 := by
  apply mixedCut (data:=cut493k8p48)
  decide +kernel
theorem all493k8 : mixedBlock g493 8 0 63 := (@mixedJoin g493 8 0 48 15 (@mixedJoin g493 8 0 8 40 ck493k8p0 ck493k8p8) ck493k8p48)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck493k9p0 : mixedBlock g493 9 0 4 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck493k9p4 : mixedBlock g493 9 4 9 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all493k9 : mixedBlock g493 9 0 13 := (@mixedJoin g493 9 0 4 9 ck493k9p0 ck493k9p4)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck493k10p0 : mixedBlock g493 10 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all493k10 : mixedBlock g493 10 0 1 := ck493k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok493 : mixedTables g493 10 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g493 0 0)
  · exact (mixedEmpty g493 1 0)
  · exact (mixedEmpty g493 2 0)
  · exact (mixedEmpty g493 3 0)
  · exact (mixedEmpty g493 4 0)
  · exact (mixedEmpty g493 5 0)
  · exact all493k6
  · exact all493k7
  · exact all493k8
  · exact all493k9
  · exact all493k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low493 : Lower (vars 493) (graphGoal 493) 11 :=
  mixedLower (g:=g493) (i:=0) (hints:=13421798917) (before_sound kn494 vl494) gm493 ok493 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp493 : List (Nat × List Nat) := [(493,[])]
def kn493 := extendKnown kn494 11 mp493
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl493 : Known kn493 := extendKnown_ok vl494 low493 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm487 : graphValid g487 (boundsBefore kn493) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck487k6p0 : mixedBlock g487 6 0 1 := by
  apply mixedCut (data:=cut487k6p0)
  decide +kernel
theorem all487k6 : mixedBlock g487 6 0 1 := ck487k6p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck487k7p0 : mixedBlock g487 7 0 13 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck487k7p13 : mixedBlock g487 7 13 5 := by
  apply mixedCut (data:=cut487k7p13)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck487k7p18 : mixedBlock g487 7 18 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck487k7p19 : mixedBlock g487 7 19 14 := by
  apply mixedCut (data:=cut487k7p19)
  decide +kernel
theorem all487k7 : mixedBlock g487 7 0 33 := (@mixedJoin g487 7 0 19 14 (@mixedJoin g487 7 0 18 1 (@mixedJoin g487 7 0 13 5 ck487k7p0 ck487k7p13) ck487k7p18) ck487k7p19)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck487k8p0 : mixedBlock g487 8 0 7 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck487k8p7 : mixedBlock g487 8 7 1 := by
  apply mixedCut (data:=cut487k8p7)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck487k8p8 : mixedBlock g487 8 8 61 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck487k8p69 : mixedBlock g487 8 69 3 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck487k8p72 : mixedBlock g487 8 72 31 := by
  apply mixedCut (data:=cut487k8p72)
  decide +kernel
theorem all487k8 : mixedBlock g487 8 0 103 := (@mixedJoin g487 8 0 72 31 (@mixedJoin g487 8 0 69 3 (@mixedJoin g487 8 0 8 61 (@mixedJoin g487 8 0 7 1 ck487k8p0 ck487k8p7) ck487k8p8) ck487k8p69) ck487k8p72)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck487k9p0 : mixedBlock g487 9 0 3 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck487k9p3 : mixedBlock g487 9 3 9 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all487k9 : mixedBlock g487 9 0 12 := (@mixedJoin g487 9 0 3 9 ck487k9p0 ck487k9p3)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck487k10p0 : mixedBlock g487 10 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all487k10 : mixedBlock g487 10 0 1 := ck487k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok487 : mixedTables g487 10 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g487 0 0)
  · exact (mixedEmpty g487 1 0)
  · exact (mixedEmpty g487 2 0)
  · exact (mixedEmpty g487 3 0)
  · exact (mixedEmpty g487 4 0)
  · exact (mixedEmpty g487 5 0)
  · exact all487k6
  · exact all487k7
  · exact all487k8
  · exact all487k9
  · exact all487k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low487 : Lower (vars 487) (graphGoal 487) 11 :=
  mixedLower (g:=g487) (i:=0) (hints:=4831839829) (before_sound kn493 vl493) gm487 ok487 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp487 : List (Nat × List Nat) := [(487,[]),(499,[134,66,50,16]),(501,[118,101,133,66,32,48,16]),(502,[118,133,64,48])]
def kn487 := extendKnown kn493 11 mp487
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl487 : Known kn487 := extendKnown_ok vl493 low487 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm491 : graphValid g491 (boundsBefore kn487) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck491k9p0 : mixedBlock g491 9 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all491k9 : mixedBlock g491 9 0 1 := ck491k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok491 : mixedTables g491 9 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g491 0 0)
  · exact (mixedEmpty g491 1 0)
  · exact (mixedEmpty g491 2 0)
  · exact (mixedEmpty g491 3 0)
  · exact (mixedEmpty g491 4 0)
  · exact (mixedEmpty g491 5 0)
  · exact (mixedEmpty g491 6 0)
  · exact (mixedEmpty g491 7 0)
  · exact (mixedEmpty g491 8 0)
  · exact all491k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low491 : Lower (vars 491) (graphGoal 491) 10 :=
  mixedLower (g:=g491) (i:=0) (hints:=5637169237) (before_sound kn487 vl487) gm491 ok491 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp491 : List (Nat × List Nat) := [(491,[])]
def kn491 := extendKnown kn487 10 mp491
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl491 : Known kn491 := extendKnown_ok vl487 low491 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm367 : graphValid g367 (boundsBefore kn491) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck367k9p0 : mixedBlock g367 9 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all367k9 : mixedBlock g367 9 0 1 := ck367k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok367 : mixedTables g367 9 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g367 0 0)
  · exact (mixedEmpty g367 1 0)
  · exact (mixedEmpty g367 2 0)
  · exact (mixedEmpty g367 3 0)
  · exact (mixedEmpty g367 4 0)
  · exact (mixedEmpty g367 5 0)
  · exact (mixedEmpty g367 6 0)
  · exact (mixedEmpty g367 7 0)
  · exact (mixedEmpty g367 8 0)
  · exact all367k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low367 : Lower (vars 367) (graphGoal 367) 10 :=
  mixedLower (g:=g367) (i:=0) (hints:=4294993493) (before_sound kn491 vl491) gm367 ok367 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp367 : List (Nat × List Nat) := [(367,[]),(379,[134,66,16]),(477,[117,65,32]),(478,[134,117,33,64])]
def kn367 := extendKnown kn491 10 mp367
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl367 : Known kn367 := extendKnown_ok vl491 low367 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm255 : graphValid g255 (boundsBefore kn367) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck255k9p0 : mixedBlock g255 9 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all255k9 : mixedBlock g255 9 0 1 := ck255k9p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok255 : mixedTables g255 9 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g255 0 0)
  · exact (mixedEmpty g255 1 0)
  · exact (mixedEmpty g255 2 0)
  · exact (mixedEmpty g255 3 0)
  · exact (mixedEmpty g255 4 0)
  · exact (mixedEmpty g255 5 0)
  · exact (mixedEmpty g255 6 0)
  · exact (mixedEmpty g255 7 0)
  · exact (mixedEmpty g255 8 0)
  · exact all255k9
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower (vars 255) (graphGoal 255) 10 :=
  mixedLower (g:=g255) (i:=0) (hints:=537355861) (before_sound kn367 vl367) gm255 ok255 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp255 : List (Nat × List Nat) := [(255,[]),(447,[134,66,16])]
def kn255 := extendKnown kn367 10 mp255
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl255 : Known kn255 := extendKnown_ok vl367 low255 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm383 : graphValid g383 (boundsBefore kn255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck383k10p0 : mixedBlock g383 10 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all383k10 : mixedBlock g383 10 0 1 := ck383k10p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok383 : mixedTables g383 10 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g383 0 0)
  · exact (mixedEmpty g383 1 0)
  · exact (mixedEmpty g383 2 0)
  · exact (mixedEmpty g383 3 0)
  · exact (mixedEmpty g383 4 0)
  · exact (mixedEmpty g383 5 0)
  · exact (mixedEmpty g383 6 0)
  · exact (mixedEmpty g383 7 0)
  · exact (mixedEmpty g383 8 0)
  · exact (mixedEmpty g383 9 0)
  · exact all383k10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower (vars 383) (graphGoal 383) 11 :=
  mixedLower (g:=g383) (i:=0) (hints:=4295517781) (before_sound kn255 vl255) gm383 ok383 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp383 : List (Nat × List Nat) := [(383,[]),(479,[117,65,32])]
def kn383 := extendKnown kn255 11 mp383
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl383 : Known kn383 := extendKnown_ok vl255 low383 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm495 : graphValid g495 (boundsBefore kn383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k7p0 : mixedBlock g495 7 0 4 := by
  apply mixedCut (data:=cut495k7p0)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k7p4 : mixedBlock g495 7 4 3 := by
  apply mixedCut (data:=cut495k7p4)
  decide +kernel
theorem all495k7 : mixedBlock g495 7 0 7 := (@mixedJoin g495 7 0 4 3 ck495k7p0 ck495k7p4)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k8p0 : mixedBlock g495 8 0 4 := by
  apply mixedCut (data:=cut495k8p0)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k8p4 : mixedBlock g495 8 4 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k8p68 : mixedBlock g495 8 68 39 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k8p107 : mixedBlock g495 8 107 37 := by
  apply mixedCut (data:=cut495k8p107)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k8p144 : mixedBlock g495 8 144 64 := by
  apply mixedCut (data:=cut495k8p144)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k8p208 : mixedBlock g495 8 208 64 := by
  apply mixedCut (data:=cut495k8p208)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k8p272 : mixedBlock g495 8 272 28 := by
  apply mixedCut (data:=cut495k8p272)
  decide +kernel
theorem all495k8 : mixedBlock g495 8 0 300 := (@mixedJoin g495 8 0 272 28 (@mixedJoin g495 8 0 208 64 (@mixedJoin g495 8 0 144 64 (@mixedJoin g495 8 0 107 37 (@mixedJoin g495 8 0 68 39 (@mixedJoin g495 8 0 4 64 ck495k8p0 ck495k8p4) ck495k8p68) ck495k8p107) ck495k8p144) ck495k8p208) ck495k8p272)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k9p0 : mixedBlock g495 9 0 1 := by
  apply mixedCut (data:=cut495k9p0)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k9p1 : mixedBlock g495 9 1 55 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k9p56 : mixedBlock g495 9 56 14 := by
  apply mixedCut (data:=cut495k9p56)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k9p70 : mixedBlock g495 9 70 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k9p134 : mixedBlock g495 9 134 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k9p198 : mixedBlock g495 9 198 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k9p262 : mixedBlock g495 9 262 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k9p326 : mixedBlock g495 9 326 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k9p390 : mixedBlock g495 9 390 28 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k9p418 : mixedBlock g495 9 418 16 := by
  apply mixedCut (data:=cut495k9p418)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k9p434 : mixedBlock g495 9 434 64 := by
  apply mixedCut (data:=cut495k9p434)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k9p498 : mixedBlock g495 9 498 64 := by
  apply mixedCut (data:=cut495k9p498)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k9p562 : mixedBlock g495 9 562 64 := by
  apply mixedCut (data:=cut495k9p562)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k9p626 : mixedBlock g495 9 626 4 := by
  apply mixedCut (data:=cut495k9p626)
  decide +kernel
theorem all495k9 : mixedBlock g495 9 0 630 := (@mixedJoin g495 9 0 626 4 (@mixedJoin g495 9 0 562 64 (@mixedJoin g495 9 0 498 64 (@mixedJoin g495 9 0 434 64 (@mixedJoin g495 9 0 418 16 (@mixedJoin g495 9 0 390 28 (@mixedJoin g495 9 0 326 64 (@mixedJoin g495 9 0 262 64 (@mixedJoin g495 9 0 198 64 (@mixedJoin g495 9 0 134 64 (@mixedJoin g495 9 0 70 64 (@mixedJoin g495 9 0 56 14 (@mixedJoin g495 9 0 1 55 ck495k9p0 ck495k9p1) ck495k9p56) ck495k9p70) ck495k9p134) ck495k9p198) ck495k9p262) ck495k9p326) ck495k9p390) ck495k9p418) ck495k9p434) ck495k9p498) ck495k9p562) ck495k9p626)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k10p0 : mixedBlock g495 10 0 16 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k10p16 : mixedBlock g495 10 16 2 := by
  apply mixedCut (data:=cut495k10p16)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k10p18 : mixedBlock g495 10 18 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k10p82 : mixedBlock g495 10 82 48 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k10p130 : mixedBlock g495 10 130 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k10p194 : mixedBlock g495 10 194 7 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all495k10 : mixedBlock g495 10 0 201 := (@mixedJoin g495 10 0 194 7 (@mixedJoin g495 10 0 130 64 (@mixedJoin g495 10 0 82 48 (@mixedJoin g495 10 0 18 64 (@mixedJoin g495 10 0 16 2 ck495k10p0 ck495k10p16) ck495k10p18) ck495k10p82) ck495k10p130) ck495k10p194)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k11p0 : mixedBlock g495 11 0 5 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k11p5 : mixedBlock g495 11 5 15 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all495k11 : mixedBlock g495 11 0 20 := (@mixedJoin g495 11 0 5 15 ck495k11p0 ck495k11p5)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck495k12p0 : mixedBlock g495 12 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all495k12 : mixedBlock g495 12 0 1 := ck495k12p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok495 : mixedTables g495 12 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g495 0 0)
  · exact (mixedEmpty g495 1 0)
  · exact (mixedEmpty g495 2 0)
  · exact (mixedEmpty g495 3 0)
  · exact (mixedEmpty g495 4 0)
  · exact (mixedEmpty g495 5 0)
  · exact (mixedEmpty g495 6 0)
  · exact all495k7
  · exact all495k8
  · exact all495k9
  · exact all495k10
  · exact all495k11
  · exact all495k12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low495 : Lower (vars 495) (graphGoal 495) 13 :=
  mixedLower (g:=g495) (i:=0) (hints:=4831864405) (before_sound kn383 vl383) gm495 ok495 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp495 : List (Nat × List Nat) := [(495,[]),(507,[134,66,16]),(509,[117,65,32]),(510,[134,117,33,64])]
def kn495 := extendKnown kn383 13 mp495
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl495 : Known kn495 := extendKnown_ok vl383 low495 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm503 : graphValid g503 (boundsBefore kn495) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k7p0 : mixedBlock g503 7 0 1 := by
  apply mixedCut (data:=cut503k7p0)
  decide +kernel
theorem all503k7 : mixedBlock g503 7 0 1 := ck503k7p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k8p0 : mixedBlock g503 8 0 23 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k8p23 : mixedBlock g503 8 23 15 := by
  apply mixedCut (data:=cut503k8p23)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k8p38 : mixedBlock g503 8 38 23 := by
  apply mixedCut (data:=cut503k8p38)
  decide +kernel
theorem all503k8 : mixedBlock g503 8 0 61 := (@mixedJoin g503 8 0 38 23 (@mixedJoin g503 8 0 23 15 ck503k8p0 ck503k8p23) ck503k8p38)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k9p0 : mixedBlock g503 9 0 9 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k9p9 : mixedBlock g503 9 9 4 := by
  apply mixedCut (data:=cut503k9p9)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k9p13 : mixedBlock g503 9 13 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k9p77 : mixedBlock g503 9 77 11 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k9p88 : mixedBlock g503 9 88 12 := by
  apply mixedCut (data:=cut503k9p88)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k9p100 : mixedBlock g503 9 100 32 := by
  apply mixedCut (data:=cut503k9p100)
  decide +kernel
theorem all503k9 : mixedBlock g503 9 0 132 := (@mixedJoin g503 9 0 100 32 (@mixedJoin g503 9 0 88 12 (@mixedJoin g503 9 0 77 11 (@mixedJoin g503 9 0 13 64 (@mixedJoin g503 9 0 9 4 ck503k9p0 ck503k9p9) ck503k9p13) ck503k9p77) ck503k9p88) ck503k9p100)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k10p0 : mixedBlock g503 10 0 5 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k10p5 : mixedBlock g503 10 5 2 := by
  apply mixedCut (data:=cut503k10p5)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k10p7 : mixedBlock g503 10 7 16 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k10p23 : mixedBlock g503 10 23 20 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all503k10 : mixedBlock g503 10 0 43 := (@mixedJoin g503 10 0 23 20 (@mixedJoin g503 10 0 7 16 (@mixedJoin g503 10 0 5 2 ck503k10p0 ck503k10p5) ck503k10p7) ck503k10p23)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k11p0 : mixedBlock g503 11 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k11p1 : mixedBlock g503 11 1 5 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all503k11 : mixedBlock g503 11 0 6 := (@mixedJoin g503 11 0 1 5 ck503k11p0 ck503k11p1)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck503k12p0 : mixedBlock g503 12 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all503k12 : mixedBlock g503 12 0 1 := ck503k12p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok503 : mixedTables g503 12 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g503 0 0)
  · exact (mixedEmpty g503 1 0)
  · exact (mixedEmpty g503 2 0)
  · exact (mixedEmpty g503 3 0)
  · exact (mixedEmpty g503 4 0)
  · exact (mixedEmpty g503 5 0)
  · exact (mixedEmpty g503 6 0)
  · exact all503k7
  · exact all503k8
  · exact all503k9
  · exact all503k10
  · exact all503k11
  · exact all503k12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low503 : Lower (vars 503) (graphGoal 503) 13 :=
  mixedLower (g:=g503) (i:=0) (hints:=4832298581) (before_sound kn495 vl495) gm503 ok503 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp503 : List (Nat × List Nat) := [(503,[])]
def kn503 := extendKnown kn495 13 mp503
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl503 : Known kn503 := extendKnown_ok vl495 low503 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem gm511 : graphValid g511 (boundsBefore kn503) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k8p0 : mixedBlock g511 8 0 64 := by
  apply mixedCut (data:=cut511k8p0)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k8p64 : mixedBlock g511 8 64 16 := by
  apply mixedCut (data:=cut511k8p64)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k8p80 : mixedBlock g511 8 80 15 := by
  apply mixedCut (data:=cut511k8p80)
  decide +kernel
theorem all511k8 : mixedBlock g511 8 0 95 := (@mixedJoin g511 8 0 80 15 (@mixedJoin g511 8 0 64 16 ck511k8p0 ck511k8p64) ck511k8p80)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p0 : mixedBlock g511 9 0 19 := by
  apply mixedCut (data:=cut511k9p0)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p19 : mixedBlock g511 9 19 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p83 : mixedBlock g511 9 83 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p147 : mixedBlock g511 9 147 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p211 : mixedBlock g511 9 211 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p275 : mixedBlock g511 9 275 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p339 : mixedBlock g511 9 339 24 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p363 : mixedBlock g511 9 363 64 := by
  apply mixedCut (data:=cut511k9p363)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p427 : mixedBlock g511 9 427 64 := by
  apply mixedCut (data:=cut511k9p427)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p491 : mixedBlock g511 9 491 64 := by
  apply mixedCut (data:=cut511k9p491)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p555 : mixedBlock g511 9 555 53 := by
  apply mixedCut (data:=cut511k9p555)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p608 : mixedBlock g511 9 608 64 := by
  apply mixedCut (data:=cut511k9p608)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p672 : mixedBlock g511 9 672 64 := by
  apply mixedCut (data:=cut511k9p672)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p736 : mixedBlock g511 9 736 64 := by
  apply mixedCut (data:=cut511k9p736)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p800 : mixedBlock g511 9 800 64 := by
  apply mixedCut (data:=cut511k9p800)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p864 : mixedBlock g511 9 864 64 := by
  apply mixedCut (data:=cut511k9p864)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p928 : mixedBlock g511 9 928 64 := by
  apply mixedCut (data:=cut511k9p928)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p992 : mixedBlock g511 9 992 64 := by
  apply mixedCut (data:=cut511k9p992)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k9p1056 : mixedBlock g511 9 1056 60 := by
  apply mixedCut (data:=cut511k9p1056)
  decide +kernel
theorem all511k9 : mixedBlock g511 9 0 1116 := (@mixedJoin g511 9 0 1056 60 (@mixedJoin g511 9 0 992 64 (@mixedJoin g511 9 0 928 64 (@mixedJoin g511 9 0 864 64 (@mixedJoin g511 9 0 800 64 (@mixedJoin g511 9 0 736 64 (@mixedJoin g511 9 0 672 64 (@mixedJoin g511 9 0 608 64 (@mixedJoin g511 9 0 555 53 (@mixedJoin g511 9 0 491 64 (@mixedJoin g511 9 0 427 64 (@mixedJoin g511 9 0 363 64 (@mixedJoin g511 9 0 339 24 (@mixedJoin g511 9 0 275 64 (@mixedJoin g511 9 0 211 64 (@mixedJoin g511 9 0 147 64 (@mixedJoin g511 9 0 83 64 (@mixedJoin g511 9 0 19 64 ck511k9p0 ck511k9p19) ck511k9p83) ck511k9p147) ck511k9p211) ck511k9p275) ck511k9p339) ck511k9p363) ck511k9p427) ck511k9p491) ck511k9p555) ck511k9p608) ck511k9p672) ck511k9p736) ck511k9p800) ck511k9p864) ck511k9p928) ck511k9p992) ck511k9p1056)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p0 : mixedBlock g511 10 0 8 := by
  apply mixedCut (data:=cut511k10p0)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p8 : mixedBlock g511 10 8 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p72 : mixedBlock g511 10 72 46 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p118 : mixedBlock g511 10 118 53 := by
  apply mixedCut (data:=cut511k10p118)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p171 : mixedBlock g511 10 171 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p235 : mixedBlock g511 10 235 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p299 : mixedBlock g511 10 299 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p363 : mixedBlock g511 10 363 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p427 : mixedBlock g511 10 427 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p491 : mixedBlock g511 10 491 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p555 : mixedBlock g511 10 555 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p619 : mixedBlock g511 10 619 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p683 : mixedBlock g511 10 683 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p747 : mixedBlock g511 10 747 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p811 : mixedBlock g511 10 811 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p875 : mixedBlock g511 10 875 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p939 : mixedBlock g511 10 939 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1003 : mixedBlock g511 10 1003 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1067 : mixedBlock g511 10 1067 12 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1079 : mixedBlock g511 10 1079 64 := by
  apply mixedCut (data:=cut511k10p1079)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1143 : mixedBlock g511 10 1143 64 := by
  apply mixedCut (data:=cut511k10p1143)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1207 : mixedBlock g511 10 1207 45 := by
  apply mixedCut (data:=cut511k10p1207)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1252 : mixedBlock g511 10 1252 64 := by
  apply mixedCut (data:=cut511k10p1252)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1316 : mixedBlock g511 10 1316 64 := by
  apply mixedCut (data:=cut511k10p1316)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1380 : mixedBlock g511 10 1380 64 := by
  apply mixedCut (data:=cut511k10p1380)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1444 : mixedBlock g511 10 1444 64 := by
  apply mixedCut (data:=cut511k10p1444)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1508 : mixedBlock g511 10 1508 64 := by
  apply mixedCut (data:=cut511k10p1508)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1572 : mixedBlock g511 10 1572 64 := by
  apply mixedCut (data:=cut511k10p1572)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1636 : mixedBlock g511 10 1636 64 := by
  apply mixedCut (data:=cut511k10p1636)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1700 : mixedBlock g511 10 1700 64 := by
  apply mixedCut (data:=cut511k10p1700)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1764 : mixedBlock g511 10 1764 64 := by
  apply mixedCut (data:=cut511k10p1764)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1828 : mixedBlock g511 10 1828 64 := by
  apply mixedCut (data:=cut511k10p1828)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1892 : mixedBlock g511 10 1892 64 := by
  apply mixedCut (data:=cut511k10p1892)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k10p1956 : mixedBlock g511 10 1956 44 := by
  apply mixedCut (data:=cut511k10p1956)
  decide +kernel
theorem all511k10 : mixedBlock g511 10 0 2000 := (@mixedJoin g511 10 0 1956 44 (@mixedJoin g511 10 0 1892 64 (@mixedJoin g511 10 0 1828 64 (@mixedJoin g511 10 0 1764 64 (@mixedJoin g511 10 0 1700 64 (@mixedJoin g511 10 0 1636 64 (@mixedJoin g511 10 0 1572 64 (@mixedJoin g511 10 0 1508 64 (@mixedJoin g511 10 0 1444 64 (@mixedJoin g511 10 0 1380 64 (@mixedJoin g511 10 0 1316 64 (@mixedJoin g511 10 0 1252 64 (@mixedJoin g511 10 0 1207 45 (@mixedJoin g511 10 0 1143 64 (@mixedJoin g511 10 0 1079 64 (@mixedJoin g511 10 0 1067 12 (@mixedJoin g511 10 0 1003 64 (@mixedJoin g511 10 0 939 64 (@mixedJoin g511 10 0 875 64 (@mixedJoin g511 10 0 811 64 (@mixedJoin g511 10 0 747 64 (@mixedJoin g511 10 0 683 64 (@mixedJoin g511 10 0 619 64 (@mixedJoin g511 10 0 555 64 (@mixedJoin g511 10 0 491 64 (@mixedJoin g511 10 0 427 64 (@mixedJoin g511 10 0 363 64 (@mixedJoin g511 10 0 299 64 (@mixedJoin g511 10 0 235 64 (@mixedJoin g511 10 0 171 64 (@mixedJoin g511 10 0 118 53 (@mixedJoin g511 10 0 72 46 (@mixedJoin g511 10 0 8 64 ck511k10p0 ck511k10p8) ck511k10p72) ck511k10p118) ck511k10p171) ck511k10p235) ck511k10p299) ck511k10p363) ck511k10p427) ck511k10p491) ck511k10p555) ck511k10p619) ck511k10p683) ck511k10p747) ck511k10p811) ck511k10p875) ck511k10p939) ck511k10p1003) ck511k10p1067) ck511k10p1079) ck511k10p1143) ck511k10p1207) ck511k10p1252) ck511k10p1316) ck511k10p1380) ck511k10p1444) ck511k10p1508) ck511k10p1572) ck511k10p1636) ck511k10p1700) ck511k10p1764) ck511k10p1828) ck511k10p1892) ck511k10p1956)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p0 : mixedBlock g511 11 0 1 := by
  apply mixedCut (data:=cut511k11p0)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p1 : mixedBlock g511 11 1 41 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p42 : mixedBlock g511 11 42 14 := by
  apply mixedCut (data:=cut511k11p42)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p56 : mixedBlock g511 11 56 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p120 : mixedBlock g511 11 120 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p184 : mixedBlock g511 11 184 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p248 : mixedBlock g511 11 248 33 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p281 : mixedBlock g511 11 281 25 := by
  apply mixedCut (data:=cut511k11p281)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p306 : mixedBlock g511 11 306 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p370 : mixedBlock g511 11 370 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p434 : mixedBlock g511 11 434 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p498 : mixedBlock g511 11 498 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p562 : mixedBlock g511 11 562 64 := by
  apply mixedVerified
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p626 : mixedBlock g511 11 626 12 := by
  apply mixedVerified
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p638 : mixedBlock g511 11 638 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p639 : mixedBlock g511 11 639 64 := by
  apply mixedCut (data:=cut511k11p639)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p703 : mixedBlock g511 11 703 64 := by
  apply mixedCut (data:=cut511k11p703)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k11p767 : mixedBlock g511 11 767 15 := by
  apply mixedCut (data:=cut511k11p767)
  decide +kernel
theorem all511k11 : mixedBlock g511 11 0 782 := (@mixedJoin g511 11 0 767 15 (@mixedJoin g511 11 0 703 64 (@mixedJoin g511 11 0 639 64 (@mixedJoin g511 11 0 638 1 (@mixedJoin g511 11 0 626 12 (@mixedJoin g511 11 0 562 64 (@mixedJoin g511 11 0 498 64 (@mixedJoin g511 11 0 434 64 (@mixedJoin g511 11 0 370 64 (@mixedJoin g511 11 0 306 64 (@mixedJoin g511 11 0 281 25 (@mixedJoin g511 11 0 248 33 (@mixedJoin g511 11 0 184 64 (@mixedJoin g511 11 0 120 64 (@mixedJoin g511 11 0 56 64 (@mixedJoin g511 11 0 42 14 (@mixedJoin g511 11 0 1 41 ck511k11p0 ck511k11p1) ck511k11p42) ck511k11p56) ck511k11p120) ck511k11p184) ck511k11p248) ck511k11p281) ck511k11p306) ck511k11p370) ck511k11p434) ck511k11p498) ck511k11p562) ck511k11p626) ck511k11p638) ck511k11p639) ck511k11p703) ck511k11p767)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k12p0 : mixedBlock g511 12 0 10 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k12p10 : mixedBlock g511 12 10 3 := by
  apply mixedCut (data:=cut511k12p10)
  decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k12p13 : mixedBlock g511 12 13 47 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k12p60 : mixedBlock g511 12 60 42 := by
  apply mixedVerified
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all511k12 : mixedBlock g511 12 0 102 := (@mixedJoin g511 12 0 60 42 (@mixedJoin g511 12 0 13 47 (@mixedJoin g511 12 0 10 3 ck511k12p0 ck511k12p10) ck511k12p13) ck511k12p60)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k13p0 : mixedBlock g511 13 0 2 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k13p2 : mixedBlock g511 13 2 8 := by
  apply mixedVerified
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all511k13 : mixedBlock g511 13 0 10 := (@mixedJoin g511 13 0 2 8 ck511k13p0 ck511k13p2)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ck511k14p0 : mixedBlock g511 14 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem all511k14 : mixedBlock g511 14 0 1 := ck511k14p0
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem ok511 : mixedTables g511 14 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g511 0 0)
  · exact (mixedEmpty g511 1 0)
  · exact (mixedEmpty g511 2 0)
  · exact (mixedEmpty g511 3 0)
  · exact (mixedEmpty g511 4 0)
  · exact (mixedEmpty g511 5 0)
  · exact (mixedEmpty g511 6 0)
  · exact (mixedEmpty g511 7 0)
  · exact all511k8
  · exact all511k9
  · exact all511k10
  · exact all511k11
  · exact all511k12
  · exact all511k13
  · exact all511k14
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low511 : Lower (vars 511) (graphGoal 511) 15 :=
  mixedLower (g:=g511) (i:=0) (hints:=4832323157) (before_sound kn503 vl503) gm511 ok511 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mp511 : List (Nat × List Nat) := [(511,[])]
def kn511 := extendKnown kn503 15 mp511
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem vl511 : Known kn511 := extendKnown_ok vl503 low511 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem exactLower : ∀ t, PEqualNP.MetaComplexity.HasCircuitSize 9 edge11008 t → 15 ≤ t :=
  conclude11008 (mixedRoot (g:=g511) (before_sound kn503 vl503) gm511 ok511 (k:=14) (by decide) (i:=0) (by decide +kernel))

end PEqualNP.Outside.L_meta_11008

theorem PEqualNP.Outside.L_meta_11008 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) t → 15 ≤ t := PEqualNP.Outside.L_meta_11008.exactLower

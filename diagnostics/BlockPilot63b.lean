import PEqualNP.Defs

-- The Live/Run/Forest checker derives from PressF10, pequalnp-proofs PR 4332,
-- and its extension in L_meta_3853, licensed under Apache-2.0.
-- The four-cell formula obstruction adapts the argument developed for L_meta_670.
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
def motifEval {u : Nat} (t : Nat) (v : Nat → BitVec u) : Nat → Nat → BitVec u
  | 0,p => if t.testBit p then BitVec.allOnes _ else 0
  | d+1,p =>
    (v d &&& motifEval t v d (p+2^d)) ||| (~~~(v d) &&& motifEval t v d p)
theorem motifBit {u : Nat} (t : Nat) (v : Nat → Sig) (w : Nat → BitVec u) (r : Row) (s : Fin u) (d p : Nat)
    (e : ∀ j<d, bit r (v j)=(w j).getLsbD s.val) :
    bit r (motifEval t v d p)=(motifEval t w d p).getLsbD s.val := by
  induction d generalizing p with
  | zero =>
    simp only [motifEval]
    split
    · simp only [bit,BitVec.getLsbD_allOnes,r.isLt,s.isLt,decide_true]
    · simp [bit, BitVec.getLsbD]
  | succ d ih =>
    have eqd := e d (by omega)
    have small : ∀ j<d, bit r (v j)=(w j).getLsbD s.val := fun j hj => e j (by omega)
    have p1 := ih (p+2^d) small
    have p0 := ih p small
    simp only [motifEval,bit,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,
      r.isLt,s.isLt,decide_true,Bool.true_and] at eqd p1 p0 ⊢
    rw [eqd,p1,p0]
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  if 65536 ≤ m then motifEval (m >>> 16) x 4 0 else
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


abbrev Bits := BitVec 63
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 63 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 63 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 63 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 63 → Row) (x : Decor) := x.2 = pairSig r s x.1
def dneg (x : Decor) : Decor := (neg x.1,~~~x.2.1,~~~x.2.2)
def dbin (d : Bool) (x y : Decor) : Decor :=
  if d then (bin d x.1 y.1,x.2.1 ||| y.2.1,x.2.2 ||| y.2.2)
  else (bin d x.1 y.1,x.2.1 &&& y.2.1,x.2.2 &&& y.2.2)

theorem ofRows_neg (r : Fin 63 → Row) (a : Sig) : ofRows r (neg a) = ~~~ofRows r a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := ofRows_bit r (neg a) ⟨j,hj⟩
  rw [bit_neg,←ofRows_bit r a ⟨j,hj⟩] at h
  simpa only [BitVec.getLsbD_not,hj,decide_true,Bool.true_and] using h
theorem ofRows_bin (r : Fin 63 → Row) (d : Bool) (a b : Sig) :
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

def asRow (cols : Nat → Bits) (i : Fin 63) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 63) (j : Fin 9) :
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
  if 65536 ≤ m then motifEval (m >>> 16) x 4 0 else
    (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 1 &&& x 8) ||| (x 3 &&& x 8) ||| (x 4 &&& x 8) ||| (x 6 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 63) (j : Fin 9) :
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
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 63) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then (if m.testBit 9 && j == 4 then ~~~(v 4) else v j) else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  by_cases big : 65536 ≤ m
  · simp only [graphGoal,liftGoal,big,if_true]
    apply motifBit
    intro j hj
    exact bit_vertex m v i ⟨j,by omega⟩
  ·
    simp only [bit,graphGoal,liftGoal,big,if_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
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
    if (rs ||| column d z.2) != BitVec.allOnes 63 then true else
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
  change covered (decide (child.length = cap)) (pairSig r s) child = BitVec.allOnes 63 at sep
  rw [deq] at sep
  change column d (pairSig r s z.1) ||| covered d (pairSig r s) (rest.map Prod.fst) = _ at sep
  change z.2 = pairSig r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((restCov (getCov (preCov ws) d) (column d a.2) (column d b.2) (op==2) ka kb ||| column d z.2) != BitVec.allOnes 63) = false := by simp [sep]
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

structure LocalSamples (m : Nat) where
  table : Nat → Bits × Bits
  ready : properPairs (chartGoal m) (asRow fun j => (table j).1) (asRow fun j => (table j).2)
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
  pick : Nat → Nat → Option (LocalSamples mask)

def wiresOf (g : Forest) :=
  rawDecor g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
theorem wires_faithful (g : Forest) : ∀ a ∈ wiresOf g,
    faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) a :=
  raw_faithful g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)

def targetOf (g : Forest) := chartGoal g.mask
def chartSamples (m : Nat) (v : Nat → Bits) := liftGoal m v
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 63) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val :=
  bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 63) (hq : chartSamples m q = 0) :
    properPairs (chartGoal m) (asRow p) (asRow q) := by
  intro i
  simp only [chart_bit,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp
def localColumns (g : Forest) (k i : Nat) : Nat → Bits × Bits :=
  match g.pick k i with
  | none => g.samples
  | some h => h.table
def localWires (g : Forest) (k i : Nat) :=
  rawDecor g.mask (fun j => (localColumns g k i j).1) (fun j => (localColumns g k i j).2)
theorem localFaithful (g : Forest) (k i : Nat) : ∀ a ∈ localWires g k i,
    faithful (asRow fun j => (localColumns g k i j).1) (asRow fun j => (localColumns g k i j).2) a :=
  raw_faithful _ _ _
theorem localPairs (g : Forest) (k i : Nat)
    (h : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2)) :
    properPairs (targetOf g) (asRow fun j => (localColumns g k i j).1)
      (asRow fun j => (localColumns g k i j).2) := by
  cases e : g.pick k i with
  | none => simpa only [localColumns,e] using h
  | some s => simpa only [localColumns,e,targetOf] using s.ready
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
  let raw := localWires g k i
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
  let raw := localWires g k i
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
  apply node_sound (raw:=vars g.mask) (localPairs g k i samples) _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply decode_faithful _ _ _ _ _ (localFaithful g k i) v
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 63) &&
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
def lanePlace (v : Nat) (upper : Nat) := 2^64*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^64 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<64 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<64 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<64 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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

def fullMarks (r packed : Nat) := ((packed+r) >>> 63) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (64*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^64)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 64*(i+1)-64=64*i := by omega
      have ge : ¬64*(i+1)<64 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 63 = (a==BitVec.allOnes 63) := by
  by_cases h : a=BitVec.allOnes 63
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^63-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^63 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (64*i) =
      (f xs[i]==BitVec.allOnes 63) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^64*u+x+(2^64*v+1)=2^64*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^64 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬64*(i+1)+63<64 := by omega
      have di : 64*(i+1)+63-64=64*i+63 := by omega
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
theorem top_xor (a : Bits) : BitVec.allOnes 63 ^^^ a = ~~~a := BitVec.allOnes_xor
theorem packed_op {α} (a b : α → Decor) (xs : List α) (op : Nat) :
    packedOp (units xs.length*(BitVec.allOnes 63).toNat) op
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 64) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (64*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 64) (i:=i) (by simpa using hi) _ ok.2
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
    let z := packedOp (r*(BitVec.allOnes 63).toNat) op a b'
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
      if len>k then true else if combField xs[q] d (op==2) ka kb op i j != BitVec.allOnes 63 then true
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
        packedColumn d (packedOp (r*(BitVec.allOnes 63).toNat) op a b))) xs) = true at pass
    rw [if_neg small] at pass
    have chosen : cov = packedCov (fun c => getCov c.2.2.2.1 d) xs := by
      dsimp only [cov]
      cases d <;> rfl
    have ca : a = _ := laneWire_at k n xs hi
    have cb : b = _ := laneWire_at k n xs hj
    dsimp only [r] at pass
    rw [ca,cb,packed_op,packed_column,packed_column,packed_column,chosen,takePacked_ok,lanes_or] at pass
    by_cases hit : combField xs[q] d (op==2) ka kb op i j = BitVec.allOnes 63
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
  let raw := localWires g k i
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

def kwCodes (i : Nat) : Nat := (if i < 1 then 0x111040220210852a11104022021085261110402202108522111040220210851e111040220210850211104022021084e611104022021084e211104022021084de11104022021084c211104022021084a21110402202108482111040220200850211104022020084c211104012061085221110400602108522111040020210852a11104002021085261110400202108522111040020210851e11104002021084e611104002021084e211104002021084de111040020210849e10c21104080921ce10c080c208288a0610c080c2082889e210c080c2082889c610c080c2082889c210c080c20828898610c080c20828890610c080c20828888210c08042080889c610c080420808894610c080420800890210a13012082a81da10a13002082a81d610a111028829216210a111028829215e10a11002002a821a10a11002002a81d610a100c4040911ca1092081011010416109208009141040e1092080011410612109208001141060e10920800114105d210920800114104161092080011410412109208001141040e10910c005121041210910c001121065610910c001121061610910c001121061210910c00112105d210910c001121058e10910c001121041210910c001121040e109108181921041a1091081019210616109108101921042a10910810192104261091081019210422109108101921041e109108101921041a10910810192104161091081019010412109108101121041a1091081011210416109108101121041210910810110104161091080819210416109108081121041a109108081121041610910800916104161091080091610412109108005921041610910800512104161091080051210412109108001921041a10910800192104161091080011610412109108001161040e10910800112106621091080011210656109108001121061e109108001121061610910800112105e210910800112105d210910800112104261091080011210422109108001121041e109108001121041a1091080011210416109108001121041210910800110104161091080011010412109108000121069610910800012106561091080001210616109108000121061200000000000c0b0400000000000c0210000000000009219000000000000905000000000000090088000000000009008400000000000822100000000000082110000000000008090400000000000808840000000000080104000000000006028000000000000601100000000000040904000000000004088400000000000301200000000000021088000000000001211000000000000105800000000000010120000000000001011000000000000061100000000000004904000000000000290400000000000028840000000000000c8400000000000009840000000000000500 else (if i < 2 then 0x22420404092121262228180043021216222818004302109a2228100243021056222810004302125a22281000430210a6222810004302109e222810004302109a2228100043021096222810004302105a22281000430210562228100043021052222810004302104e222418004282125a222410124282109e222410104282109e222410104282109a222410024382129a22241002438210aa22241002438210a6222410024382109e222410024382109a222410024382105a222410024282125a22241002428210aa222410024282109e222410024282109a222410024282105a222410014282109a222410006292105a222410004382109a222410004282129a222410004282125a22241000428210aa22241000428210a6222410004282109e222410004282109a2224100042821096222410004282105a2224100042821052222410000282125620c211040c09220e20c211040c0921ce20c211040c09214e20c201040809218e20c201040809214a20a80c001600840e20a804001600841620a804001600841220a120840c09118a20a120840c09114a20a120840c09114620a120840c01114620a101a40449110620a101840441108220a100c60409110a20a100c40419118620a100c40419110a20a100c4040911c620a100a40409110620a100840c0110c220a100840409118a20a100840409114a20a100840409114620a100840409110a20a100840409110620a100840401114620a10084040110c220a100040409116a20a100040409116620a1000404091122115020042304085a11422000616408661142200021440862114220002144085e1142200021440856114220002104085e114220002104085a11241806029282961124180602928252112418060292821611241806029281d21124180202928296111070220610854211106022061085421110602202108682111060220210860211106022021085421110602202108522111060220210850211106022021084c211105062061084c211105022061086421110502206108602111050220610854211105022061085261110502206108522111050220610850211105022021085421110502202108522111050220210850211105022021084de11105022021084c2111040a202108502111040a2021084de111040a2021084c2111040620210850211104062021084c211104026021085e2111040260210852211104026021084e211104023029084e21110402206108602111040220610854211104022061085261110402206108522111040220610850211104022061084de111040220290850211104022021086821110402202108642111040220210861e111040220210860211104022021085e611104022021085c211104022021085a611104022021085821110402202108542 else 0xa018885003040a06a0188850030409c6a0188850030409c2841108100065010a812402100414421281240210041441ce812402100414418e811211100614220e811201100214220e81120110021421ce811201100214218e811201100214214a81104818041d019281104810001d0192504080420c0088c250190488030211ca48088c0c0292829648088c0c0292825e48088c0c0292825248088c0c0292821a48088c0c029281d648088c0c0292819648088c0c0292819248088c0c0292815248088c08029282524808840c02928192480884080092814e425008104c011052425008004c01100e42440208082241d2424402080822418e424088420c008946420884088072814e420884082032810a420884080032814e420884080032810e420884080032810a42088408003280ca42086418082a825e42086408082a821242084508802a819242084408203280c642084408002a81d642084408002a819242084408002a815242084408002a814e42084408002a810a42084408002a80c624502008860420e2245020088604209e245020008204209a24442002838420e22440a0088614225e2440a0008214225e242101c40451110624210184245111062421018404411106242100c4045111c6242100c4045111062421008404411146242100840441110624210084044110c624210084044110c2242100840401114a242100840401110a24210084040110c62244240601a5025a2244240601a281e2224205040921218e224205040921214e224205040921214a224205040921210a224205040901214a))
def kwIndex (i : Nat) := packedAt kwCodes (64*i) 64
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
  (List.range n).all (fun j => termCheck (targetOf g) (stateSet g k (a+j)) k (kwIndex (packedAt data (9*j) 9)))
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
abbrev Tiny := BitVec 16
abbrev Row16 := Fin 16
def obs16 (a : Tiny) (i : Row16) := a.getLsbD i.val
def compress16 (j : Row) : Row16 := Fin.ofNat 16 j.val
def read16 (rows : Row16 → Row) (v : Sig) : Tiny :=
  (BitVec.ofBoolListLE (List.ofFn fun r => bit (rows r) v)).cast (List.length_ofFn)
theorem obs_read16 (rows : Row16 → Row) (v : Sig) :
    obs16 (read16 rows v) = restrictRows rows (observe v) := by
  funext i
  simp only [obs16,read16,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt,restrictRows,observe]

theorem availMap {R S : Type} (f : S → R) {b : List (Wire R)} {v} (h : Available b v) :
    Available (b.map (restrictRows f)) (restrictRows f v) := by
  rcases h with mem | ⟨t,eq⟩
  · exact Or.inl (List.mem_map_of_mem mem)
  · exact Or.inr ⟨t,by rw [eq];rfl⟩
theorem reachMap {R S : Type} (f : S → R) {rs k bank} (h : Reach rs k bank) :
    Reach (rs.map (restrictRows f)) k (bank.map (restrictRows f)) := by
  induction h with
  | start => exact Reach.start
  | one h ha ih => exact Reach.one ih (availMap f ha)
  | two d h ha hb ih =>
    cases d
    · exact Reach.two false ih (availMap f ha) (availMap f hb)
    · exact Reach.two true ih (availMap f ha) (availMap f hb)
def MiniLower (rs : List Tiny) (v : Tiny) (c : Nat) :=
  ∀ q bank, Reach (rs.map obs16) q bank → Available bank (obs16 v) → c ≤ q
theorem lower16 {m rs v c}
    (low : Lower (vars m) (graphGoal m) c)
    (root : (rs.map obs16).map (restrictRows compress16) = (vars m).map observe)
    (goal : restrictRows compress16 (obs16 v) = observe (graphGoal m)) : MiniLower rs v c := by
  intro q bank h hit
  have step := reachMap compress16 h
  rw [root] at step
  have out := availMap compress16 hit
  rw [goal] at out
  exact low _ _ step out
def c16 (a : Tiny) := a==0 || a==BitVec.allOnes 16
theorem c16_sound {a : Tiny} (h : c16 a=true) : Constant (obs16 a) := by
  simp only [c16,Bool.or_eq_true,beq_iff_eq] at h
  rcases h with rfl | rfl
  · exact ⟨false,by funext j;simp [obs16]⟩
  · exact ⟨true,by funext j;simp only [obs16,BitVec.getLsbD_allOnes,j.isLt,decide_true]⟩
theorem mass16 (ys : List Tiny) : ys.countP c16 ≤ mass (ys.map obs16) := by
  induction ys with
  | nil => simp [mass]
  | cons a ys ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : c16 a
    · simp [h] <;> omega
    · have c := c16_sound h
      simp [h,c,cost] <;> omega
def planeRow (w : Nat) (r : Row16) : Row := Fin.ofNat 512 ((w >>> (9*r.val)) &&& 511)
def minorOK (rs : List Tiny) (G : Tiny) (L : Nat) (T : Sig) (ws : List Sig) (k code : Nat) :=
  let v := read16 (planeRow code) T
  let ys := ws.map (read16 (planeRow code))
  decide ws.Nodup && (v==G) && (!c16 v) && ys.all (fun y => c16 y || rs.contains y) &&
    decide (k < L+ys.countP c16)
theorem minorDone {rs G L T ws k code} (lo : MiniLower rs G L)
    (ng : ¬Constant (obs16 G)) (h : minorOK rs G L T ws k code=true) :
    Impossible T k ws.toFinset := by
  intro j t hj run
  simp only [minorOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,List.all_eq_true] at h
  let f := planeRow code
  let ys := ws.map (read16 f)
  have goal : restrictRows f (observe T) = obs16 G := (obs_read16 f T).symm.trans (congrArg obs16 h.1.1.1.2)
  have rep : (ws.map observe).map (restrictRows f) = ys.map obs16 := by
    simp only [ys,List.map_map]
    apply List.map_congr_left
    intro a _
    exact (obs_read16 f a).symm
  have hs : supply (rs.map obs16) ((ws.map observe).map (restrictRows f)) := by
    rw [rep]
    intro a ha
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp ha
    have eh := h.1.2 y hy
    simp only [Bool.or_eq_true] at eh
    rcases eh with c | mem
    · exact Or.inr (c16_sound c)
    · exact Or.inl (List.mem_map_of_mem (by simpa using mem))
  have va : ∀ q bank, Reach (rs.map obs16) q bank →
      Available bank (restrictRows f (observe T)) → L≤q := by rw [goal];exact lo
  have nc : ¬Constant (restrictRows f (observe T)) := by rw [goal];exact ng
  have count := projected_bound f (list_run run ws h.1.1.1.1 rfl) nc Reach.start hs va
  rw [rep] at count
  have n := mass16 ys
  have lt : k < L+ys.countP c16 := h.2
  omega
theorem liftPlane {rs : List Tiny} {v : Tiny} {m c : Nat} (low : Lower (vars m) (graphGoal m) c)
    (r : ((rs.map obs16).map (restrictRows compress16)).map table = vars m)
    (g : table (restrictRows compress16 (obs16 v)) = graphGoal m) : MiniLower rs v c := by
  apply lower16 low
  · have eq := congrArg (List.map observe) r
    simpa only [List.map_map,Function.comp_def,observe_table,List.map_id_fun] using eq
  · have eq := congrArg observe g
    simpa only [observe_table] using eq
theorem properPlane {v : Tiny} {p n : Row16} (pos : obs16 v p=true) (negRow : obs16 v n=false) :
    ¬Constant (obs16 v) := by
  rintro ⟨b,e⟩
  have ep := congrFun e p
  have en := congrFun e n
  change obs16 v p=b at ep
  change obs16 v n=b at en
  rw [pos] at ep
  rw [negRow] at en
  exact Bool.noConfusion (ep.trans en.symm)
structure PlaneRule where
  roots : List Tiny
  goal : Tiny
  limit : Nat
  low : MiniLower roots goal limit
  nonconst : ¬Constant (obs16 goal)
def planeChecks (g : Forest) (k start n : Nat) (rules : Nat → PlaneRule)
    (probes data : Nat → Nat) (width : Nat) :=
  (List.range n).all fun j =>
    let x := packedAt data (width*j) width
    let p := rules (x &&& 31)
    minorOK p.roots p.goal p.limit (targetOf g) (stateSet g k (start+j)) k (probes (x >>> 5))
theorem planeBlock {g k start n rules probes data width}
    (ok : planeChecks g k start n rules probes data width=true) : mixedBlock g k start n := by
  intro j lo hi
  right
  have h := List.all_eq_true.mp ok (j-start) (List.mem_range.mpr (by omega))
  have eq : start+(j-start)=j := by omega
  let x := packedAt data (width*(j-start)) width
  let p := rules (x &&& 31)
  change minorOK p.roots p.goal p.limit (targetOf g) (stateSet g k (start+(j-start))) k (probes (x >>> 5))=true at h
  rw [eq] at h
  exact minorDone p.low p.nonconst h

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
def word0r3 (i : Nat) : Nat := 0x7
def lay0r3 : Packing := (1,0,0,63,0,0,1,word0r3)
def samp0 : Array (Bits × Bits) := #[(0xf,0x5),(0x7ffffffffffffff3,0x12),(0x7ffffffffffffffc,0x7fffffffffffffe8),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols0 : IndexTree ColumnInfo := (.leaf [])
def lv0 : Nat → Packing
  | 3 => lay0r3
  | _ => emptyPacking
def ix0 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g0 : Forest := ⟨3907518471,3,fun j => samp0[j]?.getD (0,0),cols0,#[[]],lv0,ix0,noFactory,noFactorySound 3907518471,fun _ _ => none⟩
example : nodeVerified g0 3 0=true := by decide +kernel
def word1r3 (i : Nat) : Nat := 0x5e33
def lay1r3 : Packing := (1,1,0,63,0,0,1,word1r3)
def keys1k4 (i : Nat) : Nat := 0x8
def word1r4 (i : Nat) : Nat := 0x20f
def lay1r4 : Packing := (1,0,0,63,0,0,1,word1r4)
def samp1 : Array (Bits × Bits) := #[(0x7fffffffffffffe3,0x2),(0x7ffffffffffffff0,0x7ffffffffffffff9),(0x1c,0x7ffffffffffffff0),(0x7fffffffffffffe0,0x7ffffffffffffff2),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols1 : IndexTree ColumnInfo := (.leaf [])
def lv1 : Nat → Packing
  | 3 => lay1r3
  | 4 => lay1r4
  | _ => emptyPacking
def ix1 : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 4 0 0 keys1k4
  | _ => fun _ => none
def g1 : Forest := ⟨2298085391,4,fun j => samp1[j]?.getD (0,0),cols1,#[[]],lv1,ix1,noFactory,noFactorySound 2298085391,fun _ _ => none⟩
example : nodeVerified g1 3 0=true := by decide +kernel
example : nodeVerified g1 4 0=true := by decide +kernel
def word6r2 (i : Nat) : Nat := 0x930c086a908119c5544408ce2aa3222650d5291131
def lay6r2 : Packing := (4,3,0,63,0,5,1,word6r2)
def keys6k3 (i : Nat) : Nat := 0xbb90002f4
def word6r3 (i : Nat) : Nat := 0x2082082083d8930c09d428ce7506339c408ce7911329e444c6791030
def lay6r3 : Packing := (6,2,0,63,0,5,1,word6r3)
def keys6k4 (i : Nat) : Nat := 0x188000da60000560000001f2880
def word6r4 (i : Nat) : Nat := 0x820820820820aa479848c180fc6778cee996e22ba63d846e187a00
def lay6r4 : Packing := (8,1,0,63,0,6,1,word6r4)
def keys6k5 (i : Nat) : Nat := 0x19000000d94000640000000c60000000000003e03c46
def word6r5 (i : Nat) : Nat := 0x20f
def lay6r5 : Packing := (1,0,0,63,0,0,1,word6r5)
def samp6 : Array (Bits × Bits) := #[(0x7ffffffffffffff3,0x52),(0x3c,0x24),(0x7fffffffffffffcc,0x7fffffffffffff88),(0x7ffffffffffffff0,0x7ffffffffffffff2),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols6 : IndexTree ColumnInfo := (.leaf [])
def lv6 : Nat → Packing
  | 2 => lay6r2
  | 3 => lay6r3
  | 4 => lay6r4
  | 5 => lay6r5
  | _ => emptyPacking
def ix6 : Nat → Nat → Option (Nat × Nat)
  | 3 => lookupWord 1 8 0 6 2 0 keys6k3
  | 4 => lookupWord 2 20 0 7 3 0 keys6k4
  | 5 => lookupWord 2 25 0 7 3 0 keys6k5
  | _ => fun _ => none
def g6 : Forest := ⟨3907649551,5,fun j => samp6[j]?.getD (0,0),cols6,#[[]],lv6,ix6,noFactory,noFactorySound 3907649551,fun _ _ => none⟩
example : nodeVerified g6 2 0=true := by decide +kernel
example : nodeVerified g6 3 0=true := by decide +kernel
example : nodeVerified g6 4 0=true := by decide +kernel
example : nodeVerified g6 5 0=true := by decide +kernel
def word61r8 (i : Nat) : Nat := 0xc96330d80bd5d2dd68b1572ad50a55127d38994b24d208d4521d08813f1ecf075391bcd8693318cc05d2d15ca8512712c9045210fc78391b0cc602d1509c48210f06c30150903c18090300c0083eeed197444ccc98eb47add42dcb6688985970f996ee196cd1130b2e1fa2ddc02d9a226165a9f4e8532d9130c32cb85edd7329b2261765970edbaa653644c2ecb2e1eb750ca6c8985d965c3e6e9994d9130bb2cb87e5d1329b2261765970fd3a0653644c2ecb2dc1774cca65d8665486b83ce8194cbb0cca90d705dd3315976199521ae0dba462b2ec332a435c1e740c565d8665486916f6e9975530cc990d724dd22dd866559321ae4b3a05bb0ccab26435c8e750b76199564086b92ce996ec332ac810d7269d22dd866559021ae4e3a25bb0ccab204370976a1b56cca865875e13ad436ad8950cb0ebc2d5a86cdb12a1961d784f350dab605432c3af0ae6a1b46c0a865875e16cd4366d8150cb0ebc2f1a86c5b02a1961d7457388e0352c310c3ae8b670dc06a58621875d178e0b80d4b0c430eba07dc969d86694861d6c4bbb2c334ad190c3ad89e76586695a021875b15cecb0cd2340430eb62d9d9619a3680861d6c5e3b2c3342d010c3ae54e711c06e4865d475cab4e1380dc90cba8eb22dcdc6a1a6619931d784bb74c336a433263af4176dd866d48664c75e16cdd30cd810cc98ebd259866d5b0219931d7a5330cda360433263af4b4619b16c08664c75e13cdd30cda90cc80ebd079b7619b5219901d7857374c3368433203af42e6dd866d08664075e16cdd30cd990cc80ebd0d9b7619b3219901d7a4b30cdab66433203af4a6619b46cc8664075e874dbb0cd910cc80ebd2a9866d1b2219901d7a5930cd9b64433203af0bc6e9866c48664075e938c336ad890cc80ebd2d1866cdb1219901d7a5c30cd9362433203ad43b75cc66c89861965a956ea18cd9130c32cb52cdd3319b226186596a5cba2633644c30cb2d8b674299619a321965
def lay61r8 : Packing := (68,6,5,63,0,9,1,word61r8)
def keys61k9 (i : Nat) : Nat := 0x1ab9dab33c29416a001e001a2400426406acad4800b600024d8b4d7c471db9c2544ae357931a6cc7e12b00001cf69e6ac000629447a1f75c5e8131641d2934cf849868600058652b648d59a381f4a9d680087666bc9fbf00041c0051007200105ba000000146927001b0400081e3a8a38898c18c0c300b1441049408420d2081441109
def cut61k8p0 (i : Nat) : Nat := 0x130984c26130984c26130984c26130984c26130984c26130984c26130984c260d0684c26130984c26130984c26130984c26130984c26130984c26130984c2611
def cut61k8p57 (i : Nat) : Nat := 0x8cee773c1acf6853b9dcee79
def word61r9 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0xa7cdc2295a3a6586caddb86d9a3a6586975dc3aed8665486b55dc32e99765486b579c02e99765486b55dc32d59765486b56dc22d59765486b579c02d5976548687ddcaaed8664c86b74dc22dd9564c86b759c02dd9564c8697d9c3aed8664086b5b9c42d59764086b5d9c32d59764086b5e9c22d59764086b5f1c12d59764086b739c42dd9564086b759c32dd9564086b769c22dd9564086b771c12dd956408696ddc3aeda865875d65db56cca865875d4f5b76c4a865875d675b56c4a865875d6b5b46c4a865875d6d5b36c4a865875d4f9b76c0a865875d679b56c0a865875d6b9b46c0a865875d6d9b36c0a865875d6e9b26c0a865875d6f1b16c0a86587587ddc3aeda961875a6ddc3aa99661875c7b9b46c1a921875c7d9b36c1a921875c7e9b26c1a921875c7f1b16c1a921875e47da7659a521875e65d96695a321875e1f99869da021875e4f9a7659a021875e37998695a021875e67996695a021875e6b996691a021875e3d99868da021875e6d99668da021875e3e998689a021875e6e996689a021875e6f196685a02187597d5c12e1a664c7597d9c02e1a664c7587dccb6a1a664c7587ddcaaed8664c7587dccbaa98664c75e2dda86998664c75c75dba6d48664c75d55db76d48664c75c7d9ba6c08664c75d5d9b76c08664c75d759b56c08664c75d799b46c08664c75d7c9b26c08664c75d7d1b16c08664c7597d9c3aed8664075c5f9ba6dc8664075c779ba6d48664075d579b76d48664075c7b9ba6d08664075d5b9b76d08664075d739b56d08664075c7d9ba6cc8664075d5d9b76cc8664075d759b56cc8664075d799b46cc8664075c7e9ba6c88664075d5e9b76c88664075d769b56c88664075d7a9b46c88664075d7c9b36c88664075c7f1ba6c48664075d5f1b76c48664075d771b56c48664075d7b1b46c48664075d7d1b36c48664075d7e1b26c48664075a6edc62dda226165a76dc52dda226165a7adc42dda226165a7cdc32dda226165a7e5c12dda226165a7e9c02dda226165a5edc72d9a226165a76dc52d9a226165a7adc42d9a226165a7cdc32d9a226165a7e5c12d9a226165a7e9c02d9a226165a7e9c0a65a226165a7e5c2261a125d65a5f5c12e5a721965a5f9c0a65a721965a7b9c0a65a421965a7d9c0a65a321965a7e9c0a65a221965a7f1c0a65a12196587f9cba65a02196587ecca6c8985d96587ddc3aeda666065979dc3aed866506597b9c02e17665065e07eaa65d8665486d25ebb6199564c86d27abb6199564086a2dcc9a21a321a66c2dda86cca865875a2ddc9619a321875c2ddba6188664c75d2d9866cc8664075b07cc961d7661565e25da9619a321a55e85da7619a321a55e86da7619a221a55ea2d86691a221a55ea4d8668da221a55ea3986691a021a55ea598668da021a55ea7186685a021a55 else 0xae75c12dda521a66ae79c02dda521a6696decc6cca865875c6deaa6cca865875c6dda86cca865875d2dda86cca86587596f6cc6c4a865875c6f6aa6c4a865875c6f5a86c4a86587596facc6c0a865875c6faaa6c0a865875d2f9a86c0a865875c3dda86cca865875c3f9a86c0a865875b2ddc32e19661875b2f9c02e19661875a67ecc659a521875c67ebb659a521875a6decc659a321875c6debb659a321875e2ddc8659a321875a6ddc9619a321875e2dd98619a321875a3facc661a021875c3fabb661a021875a6facc659a021875c6fabb659a021875e2f9c8659a021875a3f9c9619a021875e2f996619a021875b2ddc32d99899875b2f5c12d99899875b2f9c02d99899875d27d986d48699875d2dd986cc8699875d2f5986c48699875d2f9986c08699875975dc52e1a664c7587decc6e88664c75c6ddba6188664c75975ecc6d48664c75c75eaa6d48664c7597dacc6c08664c75c7daaa6c08664c75d3d9866c08664c75a6ddca21a6664c75b65dc521a6664c75b6d5c121a6664c75b6d9c021a6664c7587facc6e88664075c3f9baa20866407595facc6dc8664075d1fa886dc8664075c3f9ba6188664075977acc6d48664075d37a886d4866407597bacc6d08664075d3ba886d08664075d6b9866d0866407597dacc6cc8664075d3da886cc8664075d3d9866cc8664075d6d9866cc866407597eacc6c88664075d3ea886c88664075d3e9866c8866407597f2cc6c48664075d3f2886c48664075d6f1866c48664075a6f9ca21a6664075b4f9c721a6664075b679c521a6664075b6b9c421a6664075b6d9c321a6664075b6e9c221a6664075b6f1c121a6664075a3f9c0aaa8865d65c3eda86c89825d65a5f5c7261a125d6593eecc6c8986196596ddc3aed989996596f5c1aed989996596f9c0aed989996596eecc6c8989996596f9c0aed9799965b2edc22618699965c774a96c49761565f07cc961d7661565f07e9961d7661565a3f9c02a1985d865c7baaa6c08765065b6b9c021e6665065ad5dc3aaa7761a55c57ebb6a5a721a55ad5dc32a67721a55ad6dc22a67721a55ad79c02a67721a55ad5ecc69da321a55e55da99dda321a55ad6ecc69da221a55ad7acc69da021a55ad79ca9dda021a55e579a99dda021a55ed3a77691a021a55ed5a7768da021a55ed6a77689a021a55ed7277685a021a558f5dc3aeda85da558f6dc2aeda85da558f7acc6c0a85da558d7ecc2e9875da55ab79c02a1865da55ba5dc32ea8899a558f5dc32ea8899a559e5dc3aed8699a55da5e886cc8699a55da6e886c88699a55da7a886c08699a559e79c02e17699a55a3f9c02a68899a55a5f9c02a67799a558f6ecc6c8a859655ab79c0aaa8859655ad79c0aaa7759655ad6dc22a27759655ab6dc22a18659655ae6dc22a26659655a7cdc22d5a3a6586) else (if i < 3 then 0xf279b76199564086f278b76199564086d2fabb6199564086d2ddc32e68821a66e87da7619a521975cadebb619a321975e2ddb9619a321975e2de99619a321975e2dda9619a321975ea5d86695a321975ea7986695a021975eab986691a021975ead98668da021975eaf186685a021975c2fdb82e2aa65875a2fecc6a0a865875c2febb6a0a865875e27da86d4a865875e2dda86cca865875e2f5a86c4a865875e2f9a86c0a86587592fdc9aed862187592fecc6e58621875c2feaa6e58621875a2fecc6a58621875e2ddc36a58621875e2f9c06a58621875b27dc9619a521875e27da9619a521875e87da7619a521875e2ddb9619a321875b2ddc9619a321875e2dda9619a321875ea5d86695a321875b2f9c9619a021875e2f9a9619a021875ea7986695a021875eab986691a021875ead98668da021875eaf186685a0218759d5dc3aed865d475957ecc6e4865d475d55dc36e4865d475d579c06e4865d475c57dba6e4865d4759d5ecc6cc865d475cd5eaa6cc865d475cd5dba6cc865d475d55db96cc865d4759d7acc6c0865d475cd7aaa6c0865d475cd79ba6c0865d475d579b96c0865d475dd39b46c0865d475dd59b36c0865d475dd69b26c0865d475dd71b16c0865d475bc5dc321a665d475bc75c121a665d475a6dcc66a1a664c75b2dcc86998664c75b2decc6188664c75d2debb6188664c75e2dcca6188664c75d2ddba6188664c75e2ddba6188664c75e2deaa6188664c75f25d866d48664c75f2d9866c08664c75d2ddb82e26664c75d2f9b62da8864075b2facc6188664075d2fabb6188664075e2f9ba6188664075f0f9b76188664075f279866d48664075f2b9866d08664075f2d9866cc8664075f2e9866c88664075f2f1866c48664075d2f9b82e26664075c3f9b82e1a0a6565c5edb72dda226165c6edb62d9a226165ae6cc66d5a226165d2ecc66c89861965b2f9c0a658621965e2de99619a321965e2dd97619a321965e2dd98619a321965e2fa99619a021965ae79c02a0a55d965b2edc2261865d9658e7dcb29ca661565ae79c029ca661565d33c986d0a661565d87db76188661565da5d866cc8661565da79866c086615658e7ecc2e97661565b17cc961d76615659e5dc3aed86594659e6dc2aed76594659e79c02e17659465967ccb6617659465d1bcb861d7665065c3f5b82e1a125a55e87da7619a521a55e8dda7619a321a55ea5d86695a321a55e8eda7619a221a55eaad86691a221a55eacd8668da221a55ea7986695a021a55eab986691a021a55ead98668da021a55eaf186685a021a55975ecc6cca765486c75eaa6cca765486c76eaa6c8a765486977acc6c0a765486c77aaa6c0a765486c57ebbaa997654869adecc6cca9a2266aaddc3aaa8861a66ae3dc42dda521a66ae5dc32dda521a66ae6dc22dda521a66 else 0xde6db56c8985d965c7f8ca6c2995d965c7faaa6c2995d965d5f9c76c2995d96597ddc3aed985d96597f5c1aed985d96597f9c0aed985d965a7edc2aa9985d965a7edc2aa8985d965c7edca6c8985d96597ecca6c8985d965c7ecca6c8985d965c7eeaa6c8985d965d5edc76c8985d965d6edc66c8985d9659eddc3aed865d96597ddc3aed989996597f5c1aed989996597f9c0aed98999658fddc32ea889996597f9c0aed979996587fdc82e997999659f5dc3aed8661565be79c02e17661565be6dc22617661565f87cc961d7661565f87cb961d76615659f6dc2aed7661565f87d872997661565be3dc42997661565bc7dc72197661565be3dc42197661565be5dc32197661565be6dc22197661565be75c12197661565be79c02197661565f87d875da6661565c7ecca6c8985d56587fccb6a6885d565c7faaa6c0a766065c7f9a66c0a766065c7ddc3aeda666065a7ddc3aeda666065c7ddc96ceaa61865a7ddc3aa99861865a7ddc3aa997618658fbdc4aeda85d8658fddc3aeda85d8658fedc2aeda85d865c7f9c96c0a85d86587fecc2e9985d86597bdc7aeda86506597becc6d9a86506597becc6d88765065d7b9ca6c08765065d7b9c66c0876506597bdcaaed866506597bdc7aed8665065d79dc3aed8665065b7b9c021d866506597bdca2e1766506597bdcb6a17665065a7f6cc6e1a125a55a7ddc32e6aa61a55a7f9c02e6aa61a55c7dcc96ceaa61a55c7dcb96ceaa61a5597ddc32e6aa61a5597f9c02e6aa61a55a7ddc3aa8a961a5587fdca2e67761a55e57cc969da521a55e5dcc969da321a55e5ecc969da221a55e5f8c969da021a558fddc3aeda85da558fedc2aeda85da55c7f8c96c0a85da5587fdcbaa8985da55c7f9ca6c0985da55c7f8ca6c0985da55c7faaa6c0985da55d5f9c76c0985da5587fecc6e0a999a55c7f9c86c0a999a55c7f8c86c0a999a55c7f9c76c0a999a55c7f8c76c0a999a55a7f9c02a4a899a55c7f9ca6c09899a55c7f8ca6c09899a558fddc32ea8899a55a7f9c02a68899a55a7f9c0261a799a55a7f9c02a4a799a55a7f9c02a58799a55a7f9c02a48799a55a7f9c02a67799a55a3fdc82a58699a55a7f9c02a58699a55a7f9c02a57699a55c75db52d5a3a6586aadcc86d9a3a6586aadcc8699a3a6586aaddc32d6aa61886aaedc22d6aa6188692fecc2ea99618869addc3aeda5618869af9c0aeda561886e27dc9aa98665486ba5dc329d8665486ba6dc229d8665486ba79c029d8665486f07cca65d8665486f07eaa65d8665486e0feaa65d8665486f07dc565d8665486f07cc565d8665486d2debb619a564c86e2dda7619a564c86d55db72dd9564c86f25ebb6199564c86f25db76199564c86f25cb76199564c86d2debb6199564c86d579b52d59764086d579b72dd9564086f27abb6199564086)) else (if i < 6 then (if i < 5 then 0x97decc6e88664c75c7ddba6988664c75c7ddba6188664c75d75da66d48664c75d75d866d48664c75d75dba6d48664c75d7d9ca6c08664c75d7d9a86c08664c75d7d9a66c08664c75d7d9866c08664c75d7d9ba6c08664c7597ddca2e26664c7597ddc62e26664c75d3dcb86a26664c75d7d9c3aed8664075c7facc6e88664075c7f9ba6188664075d5f9b76188664075d779866d48664075d7b9866d08664075d7d9866cc8664075d7e9866c88664075d7f1866c4866407597f9c62e26664075a7facc6e1a0a6565e3f9b82e1a0a6565c7f9b86dda0a6565e3f8b86a1a0a6565c7ddc76ceaa66165c7dcc76ceaa66165c7ddc66ceaa66165c7f9c86c2aa66165c7f9c76c2aa66165c7f8c76c2aa66165c7f9c66c2aa66165a7edc7aeda226165a7eecc6dda226165a7edc62dda226165a7eecc6d9a226165a7edc72d9a226165c7ecb72d9a226165c7edb76d5a226165d3f8c86c29926165a7f9c0a65a726165a7edcba65a226165a7edc7a65a226165cf6db76d5a226165a7edcaa65a226165b7e9c0a65a226165c7f9ca6c299a2165c7f8ca6c299a2165c7f9ba6c299a2165c7f8a96c299a2165a7f9c0a65a7a2165a7f9c0a65a6a2165c7f9c86c2aa65d65c7f8c86c2aa65d65c7f9c66c2aa65d65a7f9c0aaa8865d65c7edca6c89825d65c7eda86c89825d65d76db56c89825d65a7f6cc261a125d65a7f5cb261a125d65e775c5261a125d65e7e5c2261a125d6587fdcbaaa9961d65c7f9ca6c29961d65c7f8ca6c29961d65c7faaa6c29961d65c7f9ba6c29961d65c7dcc96ceaa61965cf5dc56ceaa61965cf5db56ceaa61965a7ddc3aaa9961965c7f8ca6c29961965c7faaa6c29961965d3f9c86c29961965d3f9b86c29961965a7ddc3aa99861965b3f9c0a649861965d3ee996c8986196593fdc8aed976196597f9c0aed9761965a7ddc3aa99761965af5dc3aa8a561965c7f9c06ea9921965c7f9ca6c2992196597ddc3aed982196597f9c0aed9821965a5fecc2e5a721965e5f5c12e5a721965a5fdc8a65a721965e5f9c0a65a721965a5fecc661a721965a7f9c0a65a72196597f9c0aed9721965a7bdcba65a421965a7bdc8a65a421965a7bdc7a65a421965e7b9c0a65a421965a7ddc8a65a321965a7ddc7a65a321965e7d9c0a65a321965a7decc661a321965a7decc65da321965a7ddc961da321965a7edc8a65a221965a7edc7a65a221965e7e9c0a65a221965a7eecc661a221965a7f5cba65a121965a7f5c8a65a121965a7f5c7a65a121965e7f1c0a65a121965a7f5c96dda121965aef5c66dda121965a7f6cc65da121965c7f9cba65a021965a7f9c8a65a021965a7f9c7a65a021965a7facc661a021965a7facc65da021965a7f9c961da0219659eecca6c8985d965d6eca96c8985d965dcedc76c8985d965de6dc56c8985d965 else 0xc7f9b869da564086b5f9c5aed9764086b5facc6d5976408697f9c5aed9764086b779c7aed9564086b77acc6dd956408697f9c7aed9564086c7decc6cca9a2266c7ddc56cca9a2266c7dcc56cca9a2266c7ddb56cca9a2266c7dcb56cca9a2266c3fda86dc9825666a7eecc261a225666a7edcb261a225666e3edb8261a225666a7edc7261a225666c7ddc96ceaa61975c7dcc96ceaa61975c7ddb96ceaa61975a7ddc3aa9a961975a7ddc3aaa9961975e57e9969da521975a7decc6e5a321975a7ddcba65a321975a7ddc6a65a321975a7decc6a5a321975e75e99695a321975a7facc6e5a021975a7f9cba65a021975a7f9c8a65a021975a7f9c6a65a021975cdf9b76d5a021975a7facc6a5a021975e5fa9969da021975e77a99695a021975e7ba99691a021975e7da9968da021975e7ea99689a021975e7f299685a02197587fcca6e299999758fddc32ea8899975a3fdc82a58699975d6ddc3aeda865875b2fdc8aa9a865875d6deaa6cca865875d6dda86cca865875d6f6aa6c4a865875d6f5a86c4a865875d6facc6c0a865875d6faaa6c0a865875d6f9a86c0a865875c7deaa6cca865875c7dda86cca865875d6ddc66cca865875c7f6aa6c4a865875c7f5a86c4a865875c7faaa6c0a865875c7f9a86c0a865875c7ddc36e6aa61875c7ddc96ceaa61875c7ddc3aeda961875e6ddc3aa99661875b6ddc32e19661875b6f5c12e19661875b6f9c02e1966187593fdc8aed9661875a7ddc3aa99661875c7debb6cda921875c7fabb6c1a921875e7b9b46c1a921875e7d9b36c1a921875e7e9b26c1a921875e7f1b16c1a921875a6fccbaa99621875e67ecc659a521875e67dc8659a521875a77ecc659a521875a77dc9619a521875e67d96619a521875a77ecc6a5a521875e75dc36a5a521875e76dc26a5a521875e779c06a5a521875a7decc6e5a321875e6decc659a321875e6ddc8659a321875a7decc659a321875a7ddc9619a321875e6dd96619a321875a7decc6a5a321875e7d9c06a5a321875a7facc6e5a021875e3facc661a021875e3f9c6661a021875a7facc661a021875e6facc659a021875e6f9c8659a021875a7facc659a021875a7f9c9619a021875e3f998619a021875e6f996619a021875a7facc6a5a021875e7b9c46a5a021875e7d9c36a5a021875e7e9c26a5a021875e7f1c16a5a02187587fecc6e4a899875a3fecc2e99899875a3fcca6d9989987587fecc2e998998758fddc32ea8899875b6ddc32e19699875b6f5c12e19699875b6f9c02e19699875a6fccb6a19699875e2fdb86a19699875a6fdcb2a1969987587fdcb2a19699875a6fdc62a1969987587fcca6e5869987597ddc8aeda664c7597ddcaaed8664c75c7ddcaaed8664c7597decc6e98664c75c7debb2e98664c75e3dda86998664c75c7decc6e88664c75) else (if i < 7 then 0x26492c493248123491448724212048fc47b23c11d48e446f23611a48cc46323011748b445722a114489c44b224111488443f21e10e486c43321810b4854427212108483c41b20c105482440f206102480c4032000ff47f43f71fa0fc47dc3eb1f40f947c43df1ee0f647ac3d31e80f347943c71e20f0477c3bb1dc0ed47643af1d60ea474c3a31d00e747343971ca0e4471c38b1c40e1470437f1be0de46ec3731b80db46d43671b20d846bc35b1ac0d546a434f1a60d2468c3431a00cf467433719a0cc465c32b1940c9464431f18e0c6462c3131880c346143071820c045fc2fb17c0bd45e42ef1760ba45cc2e31700b745b42d716a0b4459c2cb1640b145842bf15e0ae456c2b31580ab45542a71520a8453c29b14c0a5452428f1460a2450c28314009f44f427713a09c44dc26b13409944c425f12e09644ac2531280934494247122090447c23b10d085c428211107082c4102000fe87e83ee1f40f887b83d61e80f287883be1dc0ec87583a61d00e6872838e1c40e086f83761b80da86c835e1ac0d486983461a00ce866832e1940c886383161880c285b82d61680b2858828c1430a004f427413709a04c425c12b094049424411f08e046422c113088043421410708204041fc0fb07c03d41e40ef07603681900b60570298146096049824010607b03701ac0d0065031017c0ae04f026011007803901b00cc06002d015009c04802100f006c030015009003c018009003000c000c7dda76cca5a6586c7dca76cca5a6586c7dda66cca5a6586c7eda86c8a5a6586c7eda76c8a5a6586c7eca76c8a5a6586c7eda66c8a5a6586a7decc6d5a3a6586c7ddb76d5a3a6586a7ddc72d5a3a6586a7ddc62d5a3a6586e75db52d5a3a6586e75cb5695a3a6586a7ddc7295a3a6586a7ddc6295a3a6586e75db5295a3a6586b7cdc2295a3a6586eaddb86d9a3a6586eaddb8699a3a6586ceddc66ceaa65586cbf9c86c2aa65586c7dcca6ce9965586d75dc56ce9965586a7ddc3aa99765586a7f9c0aa99765586a7ddc3a65a72558697ddc3aed972558697edc2aed9725586c7ddc36e6aa61886c7ddc96ceaa61886d75dc66cca765486d779c86c0a765486d779c66c0a765486977dc7aed8665486d75dc3aed8665486977ecc2e98665486977dc72e98665486b75dc329d8665486b76dc229d8665486b779c029d866548697ddc3aed8665486d75dc96cca765486d779c96c0a765486b57ecc2e99765486f47dc62e99765486f55dc32e99765486f579c02e99765486b57ecc6d59765486c7ddcaaed8664c8697ddc5aed8664c8697ddc7aeda564c86b75dc7aed9564c86b75ecc6dd9564c8697ddc7aed9564c8697f9c5aeda76408697facc6e1a76408697f9c7aed866408697f9c5aed8664086d7d9c3aed866408697f9c7aeda56408697facc6e1a564086 else (if i < 8 then 0x7c931ac7f17c3f04c041041041f003040000000041041001001001001041001000041041041000041041040001061e347c5f008040041f27c5f0fc047cb041001040040001041040041041001001041001001041f1fc02707f1fc00907f1ec5f047b103b1020025f244040097c910250825f245000000060f0e0e081838247420000000000000000000000000000014e4a6f53629a54cca6353029754b4a5752a294549ca4b5242915484a3f51e28e546ca3351828b5454a27512288543ca1b50c2855424a0f506282540ca0350027f53f49f74fa27c53dc9eb4f427953c49df4ee27653ac9d34e827353949c74e2270537c9bb4dc26d53649af4d626a534c9a34d026753349974ca264531c98b4c4261530497f4be25e52ec9734b825b52d49674b225852bc95b4ac25552a494f4a6252528c9434a024f527493749a24c525c92b494249524491f48e246522c913488243521490748224051fc8fb47c23d51e48ef47623a51cc8e347023751b48d746a234519c8cb46423151848bf45e22e516c8b345822b51548a7452228513c89b44c225512488f446222510c88344021f50f487743a21c50dc86b43421950c485f42e21650ac8534282135094847422210507c83b41c20d506482f41620a504c823410207503481740a204501c80b40420150047ff3fe1fe4fec7f33f81fb4fd47e73f21f84fbc7db3ec1f54fa47cf3e61f24f8c7c33e01ef4f747b73da1ec4f5c7ab3d41e94f4479f3ce1e64f2c7933c81e34f147873c21e04efc77b3bc1dd4ee476f3b61da4ecc7633b01d74eb47573aa1d44e9c74b3a41d14e8473f39e1ce4e6c7333981cb4e547273921c84e3c71b38c1c54e2470f3861c24e0c7033801bf4df46f737a1bc4ddc6eb3741b94dc46df36e1b64dac6d33681b34d946c73621b04d7c6bb35c1ad4d646af3561aa4d4c6a33501a74d3469734a1a44d1c68b3441a14d0467f33e19e4cec67333819b4cd46673321984cbc65b32c1954ca464f3261924c8c64332018f4c7463731a18c4c5c62b3141894c4461f30e1864c2c6133081834c146073021804bfc5fb2fc17d4be45ef2f617a4bcc5e32f01774bb45d72ea1744b9c5cb2e41714b845bf2de16e4b6c5b32d816b4b545a72d21684b3c59b2cc1654b2458f2c61624b0c5832c015f4af45772ba15c4adc56b2b41594ac455f2ae1564aac5532a81534a945472a21504a7c53b29c14d4a6452f29614a4a4c5232901474a3451728a1444a1c50b2841414a044ff27e13e49ec4f327813b49d44e727213849bc4db26c13549a44cf266132498c4c326012f49744b725a12c495c4ab254129494449f24e1 else 0x0))))
def lay61r9 : Packing := (829,5,5,63,0,13,1,word61r9)
def keys61k10 (i : Nat) : Nat := (if i < 1 then 0x1a333737100101926e0544705bc14431f1903a7238d271b847e0c9926ac019607ee831cc45f0bc92a6c2d9b01701b8585c21e9b5dd0000b01aa2806c70130d88586266327663028310615442aca5ef60f9b845ec446865911d62a8e151906b30954105d046d18eb1a5c166f88fe1c2faf61286d0f7404a42c911d8000022ed5210324e00bbd1ab29b3d844b015819fa2a09c5291e3d863a2057277a30a0000e0ad903122e192cf618b233ca08af1f0513e33354048e521820a21458478d8930000e30b5c3a591bf0ab151c80cc51b5e23262fd22b35129d12c988d8033e9f7f67e0000000071ad20440ea4c1f630428002b066f19048dab2a5d182932461c050824038000088519924713c2041c167c47b00000000a0b8b2f00000b45c22510000687b9203333a0000c196f13d0179167c0000000054a791286140000000000000000000002171000014e03133316251bcd0708026729e42c8407fe2e40000213522a168a722df000002b0a89c0000000000000000a2c4000012732305032e0000213100004af4000072bfa1070000220622ae41d6f0590000d2b2e1dae012101100007312c13b50f600008c31b1c918958113415550e300008081026b000000000000e0f46278124532da708300000000d5d3c47905ee915a810fb2b5f0f5d2ea00006069d2d50224388ce00c860b529a000031d500000c5792492208d0b492e6029b2018c0101dd0b2cda14dd4e18308229d21afd317324a121e7b14020fc063a1db76ad6299a4597297b03de33822afc1bf300a421c80d50000f856c076131e73001ca479df1073f0290000000062504156e253000001ff0000c0f0f27f00000000003571d3321365e6517b71be0000232081c6e4752007f03700000000287db0fd304fe0daa0fa0692631dd3153c74d1852334d188962bf32dc17cfc535053f3363225b142d194b0fc3056e030030400000500041f1201010f0f02290213100665020004000c000008021b16282a0a010a1f0e10005216071d151d170013002f2d0a0000050904140629080046000102110212070a01012d090018000810081116110a2102230a2e281a04020201050503330109060601060125000100332c12050301000000050510001400002009030007000b180005130d03010b043c1d180211020101011300250003013d5204284306000f0302110a03000100121103100107070c0201000004030a050d01000700000106002700036107000101010108430e0303081c0000002112000001020106000d0600000d1700120c0b0717000c000040070535152004075103010133040b041b0a050002010b540006004b7f9504000c081c060004004b160723072a05273e000045201c0e39044203000008090001190045020115030102031b080500171c030912082a0100091100000d else (if i < 2 then 0xd8689a22ba20407000f838515b060cd0fbd4a811f3d1634296207510baf0c66149e0cb41a0c1fc9268026100007267d832b2be000072300000728300003ca740b000002130648d309896d7e0bfb258b04bd10892d1012a8164e4ddb0c70000000071ba82c6c25f306861ec2b0bd5eaa17ab2e384d0228950d7a10cc3187339f455815800c52096f00bc036604c12f2c43d912d5077e16a611fe14f31cec4d885e122ff319e61fba065825a62dee00d2b22927040ec95e5c2316023e293d12eb1c4d687b0eb85e070f321e610548139d15df07df3016227e07ab1acf1a91115c0ed51b2518742434074e1dfd117c05542cb91c82c3cf01ca91859d0008e72c0a25631f430722436e1a29ca8052013116f0ee00e52075eb8215c02bbd1e2b40870ac3138a07bf215d192905cc06fa04d6892a24f717541956aad82aa517e21b65189427a5004114c683e94e9320ee2f1309ed5fbb03f409024740152686a90bed218d1a8d23b71d440050000f8379252e06e404ea08f4263e1c1132ff0d20000f183f22130d310d1a4af601bb1ca54de49ec9100931b7c3952f98265e62a828da9f8143fe087a2e8d247f319818072a2c4df222ee05dd09d742bf02b142f110e024ca691000000000000a17281e57c2cb1d7f44ec46ef23f92750000e304b8341290416100000000d0b7f1430000d255424d9153902570eea202f211a0f8c0b96ca56080a4dc8248e83f22944830e26f30ef8b21f02750c3f123e0bd2501408d62b6c0b530a3b2bde1f592fc7089021dc24602b7922968830147e2eef223a0e821bd60cf807ca14b611ab137d21f9922b2c54aaef21491189097c46c132771c3c22660c10869522f428f61fea25bdc7bf2b462c1f5dff6bc12ecc1f9a22abdec11a37067b9cf429f572e8146d11e000062d00000000070e4e1cbe01fb0c4410b30a20000612f9079000070c020130000733b000011810000000024ff80e6a1dc0000e216707820929c37823e625d0000e22de5e7c9b466e6d9e3724b0000cc5ce08c41aaa19962c2602de42d46b8eab892f881dd32d691b78049410910b3e03be331a9a471fde07190a1b204d2a4e2bc416804aed03ed25cb1d9e1e7f09be165e0a8d23300c20000c103b006f0ea50e26326b16e70288244d03401aefb0eb306a2f57894720d0000570eb83380afd1a42116c0c8c314b0033325960435fab2a9123c12f49637b28b5008ec3572e96332131a30d9c014a26ce241216c3313e282b17dc27d8c3f4106730c71d2e89ec19c72ca484d35b0000010216316909951c700006217406a523700000197027ea0a68178000000000000e27b7136d05a523d0220f060c2ddf01e0000b9b11291c1a71111588e091900009020331f933300008064211090220000816901f230b64af7000030db5878d2db227c00fe000094ea62 else 0xf68acc72e0576c3878910000b2981874b87a428af08582fe930382a7328e11efb872a330d00163090000b22cd235518da1740000e11be050786600000000a1bb5480e114000062d23d17000000000000c28ca17000000000000040b24125000000000000d02f92dc626d915e9120014a70f110864254a201616be6a48047325e81278aa400000000a09fcc7312c3000000005636c2e72242b1980000b8798132e1a6f148f2d3d0a05284332b210aa1b00000d68851910000d04512e2f285b871532a0000410d00000000212681a130cdddc8b23900003681f71ec6931236000000000000045882d40000223438a8152242e0b84c906c20d6605f6897dc3e973200005150e88b019d216db43cd2a3bde14257e0ce4272666171de214122b86039b23ac2d8eaf5503c1061e159d279d0246dd15058b26071e1416fa0aae0ca518f90e532fab73a926991cd30a7f2b13228503240e70000a2e5706d52efd13a56ac772962c7e0a442ab29def0431160d19ba1b900000000b4459219d2cc532c71ccc328200f721bd281b016514e81eb319370d462223274615f546f4262330e0000b176101d000071ed1259000019e4f1778a04817fd443b502918409e00476f2ad130f69e8d2f7c09c2c3bf134405e5104f1c50000f12b6212f062429c883c4200c889c18614d2f2f6891c9323f45ea05122fb600962091088142a347f902cd0a5042e50529307031c42f3e18a802e042cb2ebc084a240a2ced862019a511260a934d1818c0173d22b73294264a2950157e82a802ae13f845272b9d0b1a5ec5438b0f220))
def cut61k9p0 (i : Nat) : Nat := 0x130984c26130984c26120984c26130984c2613
def face61k9p129 (i : Nat) : Nat := 0x2c4211044f700a12c0657b81808c4218440c04ae190c306020f08ad7158e13dc55881d103a213080e8854715402a5c5400a77000000c42f107500bc4288051005e20bc417882e105c20b8417082e105c214c4294052005d20ea016dc51942d09465168a2d145928b250784510049283c228802f104f70b45
def face61k9p193 (i : Nat) : Nat := 0x18443088611038321862a384f717a312025e38ba1830116dc27b85b709ee16dc3088bb010c3070627b85470a8e08825a84180974316dc2db85b710c312020c0461110c312020c04b901703151c5b8007116a101862db886196c21202570cb5084411d402c085b7154015c45a0c220964e018659845b7164e
def face61k9p257 (i : Nat) : Nat := 0x7116e02a805500aa00bc418d031a061116c2
def cut61k9p267 (i : Nat) : Nat := 0x68341a0d068340a130984c26130984c26130000026130984c26130984c26000b03c080b09844321909864161b0582c24190c86416120401c160b0a85c26130984c26130984c2613
def cut61k9p331 (i : Nat) : Nat := 0x984c260d0984c26130683426130984c26130984c26130984c26130980026130984c26130984c26130984c26130984c26130984c26130984c260d068341a0d068341a0d068341a0d
def cut61k9p395 (i : Nat) : Nat := 0x604c26130984c26130984c26130984c2613
def cut61k9p411 (i : Nat) : Nat := 0x3da74fa7d11c74462311a24462160200f62311a41228945888f47b3d9d0461e1188cf66f8ea01067b3d9f182ba6009124c0154c1b8bd372f4dc6f60302126f469bcde6f37a00de6f
def cut61k9p475 (i : Nat) : Nat := 0x3d9ecd87b3da6cf67b361ecf67b3d9b12ac53d9bcfa7d3e9f539313dcd960b05e874bc7b3d9bc74213d9ecf6233d9ed642311879661e123fd5cae2d4d5ae5a574dd5cae572b95c5b
def cut61k9p539 (i : Nat) : Nat := 0x3d944f67b119b8de7b3d994f66c372f4dcf6379bd806e389bcf67b439ecf6873ba00e46e371b846582c08e1a1d659b8786f3da00de372c1bd7a7b37a00f68037a00de6f3d9ecf66c
def cut61k9p603 (i : Nat) : Nat := 0x3e1f4f0783c1e10080402004626130b500414020100801188c4623119ecf67b3d9ed0a8542af8f2793c9e4f67b3d8a0fa7e3e218f0783c1e0fa6e5eaf4da7b3d9ed7abd371c4f67b
def cut61k9p667 (i : Nat) : Nat := 0x3c1e0f080119004a41129ec4a7b3e8acfa233d9ec467b151f4462311894f67b3f101667b3e9e4f2793ca004c8311a15068541a0d087b131ec467b3d9ecf47d3e1f0fa293e0a8fa7c
def cut61k9p731 (i : Nat) : Nat := 0x112150a8341a1046835f20d02814120c46233da150a7b151f5182a141f4fa4c3e1f0fa86431f4ac231188c46241088442211188c46378ea0cf67b3d9ed0a7d601f4fa4d3e9f10c78
def cut61k9p795 (i : Nat) : Nat := 0x4623118844221109584623598884423598884024121ed98231d9ecde2311884462341af9268f
def word61r10 (i : Nat) : Nat := (if i < 9 then (if i < 4 then (if i < 2 then (if i < 1 then 0xaa98621b2bed394eca90da9faa98665486e1fb2ec332a4372dd866959321b96ec332ac990dcbe6199564086c5fb5254d113362fd9869a8899a97e5cd10434cdab7619a321975c5fb505432c3ad2fdb9618861d717ed4b0c430ebab7619a3218759afb74432ea3ad57db9219751d6eaed990cba8eb75e6c0865d475e5bb0c433263af2f986219901d756ec3346432cbabe619a021965ccfd325330ab2ce7cba5d98559793e4c4ccc2acbb9e6c2aa59465bcf361552ca32d67db921d651978dec390eca0cb69faed8621a55d4fd54c310d2af27da961886957c3ed3b0c434abe97619a321a55f4db0cd110d2afa798668086956e3e5b30ebb4aba9f6a0a899a55d5bb0cd190d2ad6debb6199321a9fd5db0cc810d69f2d5a9a22669ddd76d112b336aee886889599a73f5db4a434cda9fa21a521a669ded76d090d3352febb662661d717ed4d11330eb9b7aaa6664c75e5bd11333263af2fa88999901d69fcd8533442cb4fb6c89861965c77d554432832e6beaa9999419795f444ccca0cb3ddaeda125a55daeceed092d2acd7db72a4869566bf5db4e434ab3d7aeda321a55dabceed190d2aee5d8668c869567b75db44434abadb619a221a559ef576d010d2aed7a77680869575bcc3340434ab3db6caaa5da559af974c3aed2acf76bb68476956f3cd8131334ab79e6c0a799a55bcf36043ccd2af87e889de66956f3ad892d334ab71f6dc8699a55bc7b68434cd2ade5db321a66956f36d910d334ab79d6c48699a55bcf360434cd2ade75b11da669563fb5db424b4ab97d9dda125a55adf36054ccd2ad6f9b026266956baed994eca90d5db6c8a765486aef36053b2a43657eaa65d9521abaf5db2ac990d57eaed9764086aef576cab20435addb32a68899a3eed9953444cd3b76ceaa61a66d5bd10d190d336afa886808699ab6ed9950cb0eb5bd6c4a865875adf3605432c3ae67d96694861d736ecb346430eb8fe661a021875cdf32cd010c3ac7ddba219931d6baeda90cc98eb5f66c08664c758ff374433203ad5f9b7219901d6bbcda90cc80eb5ee6d08664075afb366433203ad7e9b2219901d6bf8d890cc80eb1f76ceaa661658ff36155330b2c7eebb688985963fcd8554cbacb5bb6c89899965f0fb0ebb30ab2d7b9b021d941967aed9d54c34ab1df2e6aa21a559ebb665490d2acf6db22a4869567bcd8152434ab95f6a5a721a55cebb52d190d2aed5da768c869573b6d4b44434abb5b69da221a55de5b48d110d2aef4da3688869573bcd4b40434abb5e69da021a55de7348d010d2aef59a3680869577b4d1340434abbdc685a021a559ef360542ed2ac7f9b02a6669567bcd8554b2cab3db6c8a859655e0fb2ec332a4362deaa6199321b92ec332ac990dc9e6199564086e5730cca3204372d98664d9021b978c3322c810da97619a321a55 else 0xeb9df659a521875cefb52d290c3aed7da7694861d7b3ecb34a430eb9f76e5a321875cfbb2cd190c3ae7dda968c861d7b6ecb346430ebbd7695a321875cff372d010c3ae7f998680861d73fccb340430eb9fe6a5a021875e7f330d010c3aedf9a7680861d7b7ccb340430ebbde695a021875df7348d010c3aefd9a3680861d77f4d1340430ebbfc685a0218758ffb72544cc3ae3fdba662661d71fe5d331330eb1ff2e99899875c7fb50cc4cc3ae3fca8662661d737ed432d330eb9bf2a19699875afbd76d33263ad7dcb8699931d73eed434cc98eb5f7aed8664c75afbb74c33263ae7dcba619931d73ef5530cc98ebdb76998664c75afbd76433263ad7ddba219931d73eedd10cc98ebdd76d48664c75efb360433263af6ddb8999931d6beedd4ccc98eb5f76e26664c75afb971333263af3f9b6a21901d6bfcdb510c80eb5fe2da8864075aff576c33203ad7fabb219901d73fcdd10cc80ebd7e6dc8664075eef36a433203af7b9b4219901d7becd990cc80ebdfa6c88664075efe362433203af6f9b8999901d6bfcdc4ccc80eb5fe2e26664075cff370d0532b2e7f9a8682995973f75db444c2cb9fb6dda226165cfd96ed1130b2e7edb6688985973f65b3444c2cb9fb6d5a226165aff3614c930b2e7ee99688985973f6cc3444c2cbbdb6d5a226165dedb4ad1130b2d7f9b0a66885963fe5cb4f442cb1ff6e2aa65d658ff9754432eb2d7edb2261975963fedd1304bacb5fb6c89825d65cfe930d092eb2c7febb2a587596bfcd8532c3acb3f76ceaa61965a7fb714cb0cb2d7f9b0a65865963fedd532432cb5fe6c29921965cbf972d390cb2e5fe9969c865972fecc34e432cb9efa65a421965cfbd32d190cb2e7dd9868c865973eecbb46432cb9fba65a221965cfdb30d110cb2e7f699684865973facbb42432cb9fea65a021965cff330d010cb2e7f99768086596f76d9130bb2cb5fe6c2995d965afdb644c2ecb2deddb321976596f7ad890cbb2cb7be6c0865d9658ff974cc4ccb2d7edb226266596f9eda14cc2acb75f6dc8661565bebb664330ab2df6db221985596fbcd810cc2acbe5f61d7661565afdb644c2eab2d7f9b029d981963ff5db4ccc0cb1ff6e6aa618659fbb675530c32cff9b02a1761963fe5d330bb0cb5efaeda865065af7b6cd432832f3bdb6a2194196bdedd510ca0cb5ef6da8865065af7b6c43b2832d7bebb61994196bde5c2ecca0cb1ffaeda825a55cfeb70d092d2acfddb3aa9869576bed3b4a434abb7769da321a55debb4ad190d2aededa7688869577b6d2b44434abbeb691a221a55df9b46d110d2aedf9a7680869577bcd2b40434abbee691a021a55dfb346d010d2aefe9a2680869577f8d0b40434ab3fe6c0a85da55aff3604c2ed2ac7fdb82a666956bfcd8153334ab5fe6c09899a55d5bb675530c435addb3) else (if i < 3 then 0x62434cd2adef9b021a66956b7e5caed334ab9bf2a57699a55bcfb6a3b4cd2adef5b11da669575bf4434b334abb5f9dda599a55dcfaecd2ccd2acf7db6aa9759567bedc14cbacabb5f9dca65d6559ef974c32eb2add7db721975956faed990cbacab7db6c8865d655bef360432eb2aee7ca65d97595773e544ccbacab3df2ea665d6559efb71552cb2acf7db7aa9659567bedb950b2cab7db6c8a859655d6f975442cb2aeb7eaaa21659579be5cd10b2cab3df2ea8859655beeb6253acb2acf7cba61d65956f3edb10eb2cab7de6c08759655daf9753bacb2aed7eaa9dd659576bed44eeb2cabb5f2a27759655f8f96d3bacb2acf7cba9dd65956f3e5b4eeb2cabadf2a18659655bafb6e432cb2adf3db421965956faed990cb2cab7db6c88659655beeb62432cb2adf79b021965956f3f5daecb2cabb9faa97659655ecf972bb2cb2afa7e885d965957e3e53aecb2cabf1f61d7659655f8fceebb2cb2adf75b11d96595773ed44ccb2cabb9f2a26659655adfb6c52d32c357ddb32969961abf6d914b4cb0d9f76d9a3a6586cfbb6ad1d32c367dcb568e9961b3eed33474cb0d9f7695a3a6586cfb94ad1d32c36afda869a9961b76edb3474cb0dbb7699a3a65869fbb675532ac34ff9b0aa99561abeed9d32cab0d5f76ce99255868ffb735530c434fddb3aa98621abbf5db0cca90d5df2e98665486cefb735532a435f5db329d9521afb6d914eca90d7de6c0a765486eaf974cbb2a43757eaa65d9521b2ff5532eca90dd5f6d59765486eaf96acbb2a4357debb6199321abef5db4ac990d9f769da564c86eebd76cab2643775db76559321bbae5bb2ac990d5f7aed9564c86aff576d3b204357f9b869d9021abfd5db0cc810d5feaeda564086aff370d2b204367f9a76959021bafd5db2ec810dd7e6d59764086ebf16acbb204357fabb65d9021bbbd5db2ac810ddde6dd9564086eef16ecab204357fabb6559021b3eed9953444cd3f76ceaa61a66c7fb504c12b33577db52609599b3f64c3444accd1ffaeda8259759fbb675530cbaed7da7694865d67ef5db46432eb9f76e5a321975cfbd32d190cbae7dda968c865d77aed2b46432eb3feaeda021975cff372d010cbae7fa99680865d76fcdbb40432eb9fe6a5a021975dbf34ed010cbaef79a5680865d77dcd2340432ebbf668da021975dfd344d010cbaeff1a1680865d63fedc153332eb5bf6d89899975bdbb66434ccbadef5b121a665d737edc554cb0eb5bf6e2aa65875adf9715532c3ad6febb6a1961d6b7f5d950cb0ebd9f6d4a865875edbb665432c3af6f5b12a1961d7b7cd8150cb0eb1ff6e2aa65875afbb665432c3ad7f5b12a1961d6bfcd8150cb0eb1ff6e6aa618759fbb675530c3ac7febb6a5861d737f5532cc30eb1ffaeda921875cfbb66d490c3ae7f9b06a4861d737f5532c430 else 0x6956ebf5db4e434ab9df6a5a721a55dafd553b90d2af57da99dc869576be54cee434ab79faed8621a55dafb4ec310d2aef5db768c869577ae4bb46434abbd7619a321a55debb4ed190d2afd5e7768c869577b6dbb44434abbdb25da221a55dedb0cd110d2aef6da7688869577bcdbb40434abbde25da021a55def30cd010d2aef79a768086957ebd3bb40434ab3df6e2aa5da55dafb6f552ed2aef6db2aa976956fb6d9554bb4ab3df6e0a95da559efd76d42ed2adf79b02a1769567bedd130bb4ab7de6c0985da55dafd54c3aed2afc7cb661d769567be5d30ebb4ab79f2d9875da55dcfd544b2ed2afc7d8725976957f3ad892cbb4ab7dd6c4965da559efb74c32ed2aeb7ca861976956ebedb90cbb4ab7cf6d0865da55bebb66432ed2adf6db221976956fbad890cbb4ab7de6c0865da559efd76d40ed2aeb7da826076956fbcd81303b4abb5f6a1761da55deeb70d08ed2aef7498684769577bac33423b4ab79f2e5a899a55dcfb50544cd2afe79b026266957d3edd511334abe9f2ea8899a55bcf970d3ccd2ade7db829e66956f3edc12f334ab79f2e98799a55bcf972c3ccd2afa7c9861e66957e3e53b0f334abf1f2e67799a55f8f9533bccd2afc7da89de66957e3e544ef334abf1f2627799a559efb6e544cd2acf7db62a266956f3edb151334ab79f6d89899a55bef3604c4cd2afa7db6a2266957d3e5b511334ab3df2ea8899a55bcfb6d444cd2adf79b029e66956f3edb12f334ab3df2e98799a55bcfb6c43ccd2adf79b021e669576bed44ef334abb5f2a27799a55f2fd113bccd2ade7db825a66956f3f5db0d334ab79f2e98699a55bcf972c34cd2afa7e8861a66957e3f3bb0d334abe9fa208699a55bcf972bb4cd2ade7db85da66956f3e5c2ed334ab79f6e07699a55bb7b68534ef2ac7fdb62a6779572fed44ee4b4ab9fdaeda125a55cfe970d092d2ae7f5b7684969573fa5bb424b4ab9fd9dda125a55cbf9533bb0d2acdfebb69c869572fe5cb4e434abb5f6d5a721a55dafceed290d2acfdebb68c869576ef3bb46434abbb7619a321a55debb6ad190d2acfeebb688869576f73bb44434abafb619a221a55dedb6ad110d2acffabb680869576fd3bb40434abafe619a021a55def36ad010d2acfedb2aa9769563fedc152bb4ab37f2e9875da55cdfd544b2ed2af4fd87259769571fed41303b4ab5fe6c0981da559fed76d08ed2ae7f498684769577badab423b4ab5bf6e0a999a55adfb6e54ccd2af6f9b02a666956b7e5cb51334ab5bf6dc9899a55bdf36053ccd2ad6fcb961e6695797e4c30f334ab79f6d48799a55bdf36043ccd2ad6fcb99de66956f3e5c34b334ab5bf6d89899a55c7f953444cd2ae5fca99de66956b7e5cb0d334ab73f6dc8699a55bcfb6a434cd2adebdb421a66956f6ed990d334ab7bb6c88699a55bdeb)) else (if i < 6 then (if i < 5 then 0xd619a121965d7f510d010cb2eef98668086597b3edad32bb2cbdbe6c2995d965bdf3614caecb2dcfdb726176597d3e5ad10bb2cb79f6e0a55d965bdf3614ccccb2de7db52a266596b7f5db31332cb5bf2e99899965cdf974cc4ccb2d6fdb726266596f76d9131332cbcbf2e68899965f4f96b444ccb2d6fcb9a226659797ecc511332cb79f6d4a799965bdf36053cccb2d6febb65e6659737e5d32f332cbcbfa219799965bdeb624bcccb2d6fdb961e66596b7e5cb0f332cb1ff2e99799965e5f930c34ccb2e77cb72a5855973be5492ec2acb6df6e09761565beeb624bb0ab2de7ebb29985596f3edb94cc2acbf8f6d0a661565bcfd76bb30ab2de7cba5d98559773e5d2ecc2acbb9faa97661565dcf952bb30ab2f67e995d985597d3e4c2ecc2acbf1f25d76615659ef974bb30ab2de7cba9998559773f554ccc2acbd9f2a66661565f4f9313330ab2fa7e8899985596f3edbcccc2acbe9f61e66615659dfb6e5330ab2cefcba5d985597c7ec3aecc2acb3bf2ea6661565cdfb533330ab2f2fc98999855971fed4d10baacb3bf2ea665d565cdfb53332eab2e5fda729d98196dfad894f440cb8ff661a7a20658ffb715532e32e3feaaa21971963fe5d510cb8cb3ef6d2aa61c65a7fd76cc30e32e3feaa661871978fe5bb30c38cb8ff6a68861c65e3fd10cbb0e32c7febb6a4871967f6d9554bb0cb8ff2a1985d865e3fb30c3aec32d6febb6626619797ecc511330cb5bfaed9799865adfb72c3ccc32f2fd9861e66197a7ecbb0f330cb5bf6e48799865def361552ca32df79b0aa965196fb6d9150b28cb5dfaed9859465aef974cc2ca32e77eaa661651979be54330b28cbcdf6628859465beeb6253aca32f37d9861d65196bbedc90eb28cb79f6d88759465e77b754432832f3bdb7a21941979de5bd10ca0cb9efaaa8865065e77b514432832d7bdb7a2194196bdf5db4eca0cb5ef2e1a765065e77d10d3b2832d7bdb669d94196bdf5db0eca0cb5ef6e98765065cf7974c3b2832e7beaa61d941979ded430eca0cbcefa218765065eb7b4ec3b2832d7bdba21d941973df5510eca0cbcefa208765065eb7b0e43b2832e7beaa619941979df4430cca0cb5efaed7665065cf7d54bb32832d7bdb85d9941979df442ecca0cbd6f61d7665065ed7b513332832f6be8899994197b5ed3cccca0cbdaf61e6665065ed790f3332832cf7ebb698979567bf5db504b4abb5f6a27725a55deed76d092d2aef75b8684969577ba5c3424b4abbdd6dda125a55dee96ed092d2adf76bb684969577bad43424b4abbdd69da125a55faeceed092d2acf7db7aa98695773edb554c34abbd76ceaa61a55bebb675530d2acf7db72a5869567bedd12ec34abb5faaa7761a55daf9533bb0d2adf75b1259869567bedb952434abb5faeda721a55daf972d390d2acf7ebb69c8 else 0xd11334efdb72a19599a77f5db504accdabf6a09825666dddb70d112b336eec986889599b776dbb444accdbbb25da225666b5fb6a535113353fcb96968899ad7edb14b444cd6ef6d0a5a22669df972d3511335afdb829a8899a77edad54c34cdbb76ceaa61a66bdbb675530d336afeaaa218699b73f5db4a434cdb9f6dda521a66dcf96ed290d334efebb6948699b57f4434a434cdbbd6dda121a66ddeb6ad090d33577db525c9599b57ed430c4accd3fbaeda225666d7dd10d112b3367ec976889599b776db3444accdbbb619a2256668ffb744c12cbad6fdb6260965d63fe5cd54c32eb1ffaeca9619758ffb754cb0cbac7fcb9aa8865d63fedd532432ebbb7619a321975d7f30cd010cbad6fdb8a66665d6b7e5cb51332eb5bf6e4a899975adfb6d4ccccbac7fcb96a2665d71fe54d11332eb5bf2e58699975adfb72434ccbade7db521a665d6f7cd810d332eb9bf2e2aa65875cdfd54d432c3ae6feaa2a1961d737ed4150cb0ebcbf6a0a865875c7fb505432c3ad6febb659861d797e5c32cc30eb5bfaed9621875e5fb70cb10c3ad6fdb9618861d737ed4b0c430ebcbf66186218759efd76d290c3acfdebb68c861d776ec3346430eb3feaeda021875d7f30cd010c3af2febb662661d797edd331330ebcbf2e99899875adfd76cc4cc3ad6fcba662661d797ed4331330ebcbf2a19899875a7fd76cc4cc3af2fdb6662661d797e5b331330eb4ff6e68899875e5fd10cb4cc3ad6fdb961a661d797ecc30d330eb5bf6e48699875e5fb30434cc3ade7db521a661d6f6ed990d330eb7bd6c48699875bdf360434cc3ae7deaa219931d7b6ec310cc98ebdb76ea6664c75edb971333263af6dda8999931d73ef554ccc98ebcf7a226664c75edbb4d333263af6dd86999931d7b6e434ccc98ebcfe2da8864075e7f510c33203af3fa88219901d79fcc310cc80ebdbe6188664075edf171333203af6fa88999901d79fd444ccc80ebdbe61a6664075edf10d333203ae7f8b8682995973fcdbb414cacb9fe2dda0a6565cff34ed0532b2e3feaa660985967f75db444c2cbcfb661a226165a7fb6e54d10b2d3fdb7a66885979bedad33442cbcfe6c299a2165b7f3614cd10b2d3fdb929e88596d7edb14f442cb6fd6c4a7a2165c7f952d3510b2d3fcb9696885971fe54b4b442cb6bf2d9a5a2165e6fd3252d10b2d3fdb8a6688596df6d9131442cb6df6e0a5a2165c7fd554432eb2d7f9b0a64975971fed41304bacb57f6dc9825d659fed76d092eb2e7f699684975973facc3424bacbafda21a125d65ddeb6cd092eb2e3feaa26186596df6d9130c32cb4ff2e688619659bfd76d390cb2e9fe8869c8659767ed3b0c432cb3efaeda421965d77d10d210cb2eebd86690865975ef44346432cbbb7619a321965d7dd10d110cb2cff6bb684865975fb44342432cbbb) else (if i < 7 then 0x7fedb951334ab3ff6d8a899a55cff952544cd2ad7fdb726266956bfedb131334ab3ff2ea8899a55cff953444cd2ae7fc9869e669573fe5494f334ab7fe6c0a799a559ff974c3ccd2ad7fcb961e669573fe54b0f334abcff2618799a55cff95243ccd2adff9b021e66956bfe5ccef334ab9ff2a67799a55aff972c34cd2ae7fca961a66956bfe5caed334ab9ff2a57699a55b5f970d3532c36afdb5aa98621b57e5ad54c310d6bf6d6aa61886f5bb675530c435afebb6958621b57f5534ac310dabf69da561886d5fd5452b0c435afdb72958621bd3ed294ac310db5f69ca765486f4fd54c332a437a7da76199521bd3e53b0cca90dabfaa98665486e5fb2ec332a436b7da52968899ad7f5db0c432ebabfaa98621975e5fb72c310cbaf2fcb9618865d797ed4b0c432ebcbfa658621975f4fb0cd290cbafadd8668c865d7d7cc3340432ebabf6a0a899975b5fd76c310c3aeafeaa618861d797edcb0c430ebcbf6a58621875f4fb0cd290c3afadd8668c861d7d7cc3340430ebabf6a0a899875baf970d32ea3add7db8299751d76bed314cba8eb75faed865d475dafd54c32ea3add7ebb219751d76bedd10cba8ebb5faa8865d475eafb72432ea3afd5db3219751d7ebcd810cba8ebf1f6e2665d475f8f971332ea3aed7eaa999751d6ebedc4ccba8eb75f2e2665d475f2fd11332ea3afc7d86999751d7e3e434ccba8ebabf698a6a2165b5fd76c310cb2f2fe996188659797ecbb0c432cbe9f2d58621965e5fb30c310cb2f2fd982617659773e5414abb2cbcbf261865d965dcf94e5330ab2f37c9829985597d3ec310cc2acbcdf2617661565e6f9313330ab2e9fca861d7619773edc554b28cb79f6e2aa59465bcfd76542ca32ee7eaa2a16519773ed4150b28cb79f6dca859465bcf975442ca32ee7eaaa2165196f3edbd10b28cb79f2e1a759465bcfb7053aca32de7ebb61d65196f3e5d30eb28cbb9faa98759465f4fb6d442ca32de7db6a2165196f3f5db0cb28cbb9faa98659465bcfd76bb2ca32ee7eaa5d965196f3edc2ecb28cb79f2e17659465ecfb30bb2ca32fc7d875d965197d3e4bb0c434ab6bfaed8621a55d5fd54c310d2af2fcb961886957c7ed3b0c434abe3f9dd8621a55f4fb0cd290d2afadd8668c86957d76c3344434abebe619a021a55b9f96cc3aed2af4fc985d87695757ed4151334abe9f618865d655f2fb0e43acb2af2fda869a9961b3bed294b4cb0ddb76d9a3a6586edbb4cd1d32c3577db525c9561abbf5db2a4ab0dbb76ceaa61886bdbb675530c43677db7aa99521b3bedb554ca90d5df6deaa65486cefd5453b2a43677eaa6199521aaff5db2eca90ddb7aed8664c86edbb6ac33264376dcb56199321b9fd5db0cc810dcfe6dd8664086e7f16ec33204373f9b56199021b9fc5ab0cc810d6bf6d4a9a2266f5bb6654 else (if i < 8 then 0xa766065cffd54d3b3032e7feaa29d981973fed314ecc0cb9ffaeda666065cffb6ed333032e7fcb769998196ffad894f440cb5ff2ea8865c65cff9754432e32e7feaaa2197197afe5bd10cb8cb5ff6da8865c659ffb6d5530e32efbdb4aa987196fdeda554c38cbcffaed9861c65e7fd54cc30e32d7febb661871973ff55330c38cb9ff6a68861c65e7fb314430e32f5fe8865d871979fecc34cc38cb9ffaeda921c659ffd76d310e32e7fd98698871973fedcd54c30cb3ff6deaa61865dfbb675530c32dfddb3aa986196bff5db30c30cb9ffaa99861865affd76cbb0c32d7fcba65d861973ff5532ec30cb5ff6e58761865e7fb30c3b0c32f5fd9761d86196bfedc90ec30cb3ff6e2aa5d865dfdb65552ec32dfedb2aa9761967ff5db50bb0cb7fe6c0a85d865affd76cc2ec32d7fcba661761973fe5d330bb0cb9ffaa9985d865cffb50cc2ec32cffcbaa2176197afecc30ebb0cbcff661875d865ef7d76d432832f7bdb76a194197bde5bb50ca0cbdef6d9a865065ef7b514432832f7bcb7a2194197bdf5db4eca0cbdef6e1a765065ef7970d3b2832f7be8869d94197bdedb34eca0cbdefaed8765065ef7b74c3b2832f7bda861d94197bdf4430eca0cbdef69d8765065ef7b6cc3b2832f7bda821d94197bdf5db0cca0cbdef6a18665065ef7d10c332832f7bdb761994197bde5bb0cca0cbdef69d8665065ef7b0ec332832f7bc8761994197bdf5daecca0cbdef6e17665065ef7970bb32832f7bda85d994197bdf442ecca0cbdef69d7665065ef7b0ebb32832e7febb6a0969573fedbb504b4ab9ff2dda825a55cffb513b92d2ae7fcb9aa9869567fedbd54c34abbf76ceaa61a55aff9735530d2adfddb3aa986956bff5d952c34ab9ffaa8a961a55affb6e54b0d2ae7fca969d869573fe5494ec34ab5ff2e67761a55cff9533bb0d2aedfebb69c869567ff5db4e434abd7f2e5a721a55aff9733b90d2ad7fcb9618869576fed3b0c434abbdf9dda521a55defb0cd290d2aef7da7694869577eedbb46434abbf79dda321a55dfbb0cd190d2aefdda768c869577f6dbb44434abbfb619a221a55dfdb4ed110d2aeff9b7680869577fd3bb40434abbfe619a021a55dff34ed010d2acffdb8aa9769577f6d9554bb4ab7fb6caaa5da559ffd76d42ed2adff9b02a1769573ff55130bb4ab5ff6d8985da559ff974c3aed2ae7fca961d76957b7f5512cbb4abdbf6a0965da55edf9504b2ed2af6fd87259769567fedd30cbb4ab5ff2e5865da55cff952c32ed2ae7fca921976956efedb90cbb4ab7df6d4865da55bf7b68432ed2adfddb321976956ff6d910cbb4ab7fd6c4865da55bff360432ed2acffebb6a0769573fe5cb503b4ab5ff6d8981da55aff972c30ed2aeff5b8684769577fac33423b4ab5ff6e0a999a55affb6e54ccd2af7f9b02a666956 else 0x2e7feaa661865979ff4c930c32cb7fb6c89861965aff9734430cb2d7febb65d865973fe5d32ec32cb9ffaa99761965bfeb624bb0cb2d7fdb961d86596bfe5cb0ec32cbbdfaa8a561965cffb754c90cb2d7fdb8a6486596bfedbd32432cbdfe6c29921965bff3614c90cb2d7febb660865976ff5db4e432cbb7f2e5a721965dbfd32d390cb2edfd9869c865976fedab4e432cb3ffaeda721965cffd32d390cb2e7fd9869c86596bff5db2e432cbb7f69d97219659ffb744b90cb2edfda725c86596ffad892e432cb5ff6e58721965aff972c390cb2efbe99690865977decc348432cbbef6dda421965df7b2ed210cb2efbc97690865977dedab48432cbbf7a65a321965dfbb30d190cb2efdd9768c865977ee4bb46432cbbf761da321965dfdd32d110cb2efed98688865977f6cbb44432cbbfb25da221965dfed32d090cb2eff598684865977fadbb42432cbbfd65da121965dfe92ed090cb2eff587684865977fadab42432cbbfea65a021965dff330d010cb2eff997680865977fc4bb40432cbbfe61da021965bdfd7654aecb2defdb82a576597b7e54d32bb2cb7bf6e2995d965edf952cc2ecb2defebb26176596f7e5d130bb2cbdbf2a4985d965f9fb6e4c2ecb2fe7db526176597f76d9130bb2cb7bf2e6885d965fcf96b442ecb2defcb8695765973ff55532bb2cb5ff6e2995d965ebfb6f4caecb2f7f9b0a6576596ffcd8532bb2cb5ffaed985d965cff974cc2ecb2e7feaa661765973fed4330bb2cb9ffaa8985d965bbfb6e4c2ecb2dfedb226176596bfe5cd10bb2cb7bf6da885d965bdfd76c32ecb2dff9b0a66665967fedb951332cb5ffaed9899965cff974cc4ccb2d7fdb726266596ff6d9131332cb3ff2ea8899965aff973444ccb2d7febb65e665973fe5d32f332cb9ff2a19799965bfeb624bcccb2cffcba61e66596bfedcb0f332cb5ff2e58799965ddf950bb4ccb2fe7cb55da66596fbedc12ec2acb7df6dca661565befd76c330ab2df7db721985597f3f5daecc2acbf9f2e97661565fcf972bb30ab2fe7db85d985597f3e5c2ecc2acbf9f2617661565befd76bb30ab2df7cba5d985597bbe54aecc2acb7df6e17661565fafb0ebb30ab2fe7ca65d985597f3ec32ecc2acbf9f2197661565bef9753330ab2fb7d8799985597f3ebb4ccc2acb77f6dc8661565bfbb664330ab2dfedb221985596ffcd810cc2acbbbf2e976615659ff974bb30ab2e7fda95d985597cfec3aecc2acb3ff2ea66615659ffb6c542eab2cffcbaa2175596bfe5cd10baacb9ff6a6885d565aff972c3aeab2cffcba619755973fed4b0cbaacb77f6dc865d565bf7b68432eab2dfddb321975596ff6d910cbaacb7fd6c4865d565bff360432eab2eefca85d9755967fe5d4ccbaacb9ff6deaa66065cff96f5533032e7fdb6aa998196bfedbd54cc0cb5ffaed)))) else (if i < 14 then (if i < 11 then (if i < 10 then 0x8352430ebdbfaed9621875edfb70cb10c3ad7febb658861d6bfedcb0c430eb9ff6a58621875edfb2cc310c3aef7d86694861d77eec3346430ebbfe619a0218759ffb6c544cc3af3febb662661d79fe5d331330ebcff6d99899875affd76cc4cc3ae7fdba662661d6bfe5d331330eb9ff2e99899875cffb50cc4cc3af3fca8662661d67fe5d511330ebdbf6e19699875edf970cb4cc3af6fca865a661d7b7f4432d330eb9ff2a19699875affb72c34cc3af3fd9861a661d7b7ecb30d330ebdf7aeda664c75efbb70d33263af7dcb8699931d7bef5db0cc98ebdf76e98664c75efbb4cc33263af7ddba219931d7beed310cc98ebdf76188664c75efb971333263af7dda8999931d7bef444ccc98ebdf769a6664c75efbb0d333263af7f8b6a21901d7bfd5db0cc80ebdfea218664075eff30c433203af7f8b8999901d7bfd444ccc80ebdfe61a6664075cffb6ed4532b2e7fcb76a2995973fed434f4cacbdfe6e1a0a6565eff170d0532b2f7f9b768299597bfc5bb414cacbbfe6e1a0a6565dff170d0532b2eff9b7682995977fc5bb414cacb5ff6e29926165affb6f4c930b2cffebb69c985973ff4cb4e4c2cb9ff661a7261659ffb6cd3930b2ef7da7694985977bed334a4c2cbbfbaeda226165dfdb6ed1130b2efecb7688985977f6db3444c2cbbfb2d9a226165efdd32d1130b2efeda7688985977f6d33444c2cbfdb6d5a226165cffd7654d10b2e7fdb72a6885973fe5b953442cb9ff6d8a9a2165cffb6a54d10b2cffdb72a688596bfedb953442cb9ff6ea99a2165affb714cd10b2d7fdb7a6688597bfcd8533442cb9ff2a699a2165bff3614cd10b2cffcba662885967fe5cb4f442cb9ffa65a7a2165affb7253d10b2e7fca929e88596f7edb14f442cb7fd6c4a7a2165cffd32d3510b2e7fca929a885977be5494b442cbbdf29ca5a2165def94c52d10b2d7febb2a197596bfe5d510cbacb9ff2ea8865d65cffd554432eb2d7fdb6a2197596bff5d930cbacbdfb6c89865d65aff9734432eb2d7fdb8a64975967ff5db504bacb9ffa65a825d659ffb6cd412eb2d7febb260975973fed41304bacbddf6d49825d65efdb644c12eb2cffdba26097596ff6d91304bacb5ff2e68825d65dfeb70d092eb2eff498684975977fb443424bacbbfd6d9a125d65cffd7654b0eb2e7fdb62a5875973feda952c3acb5ffaeca961d65cffb754cb0eb2d7fcbaa65875973ff55532c3acb5ff6e29961d65eff3614cb0eb2cffdbaa65875973fe54d32c3acb7fe6c29961d65cff952d330eb2e7fca929987596ffad894cc3acb5ff2e5a561d65cff952d2b0eb2cffdb7aa9865977bedad54c32cbbf76ceaa61965befb6b5530cb2dfddb3aa9865973ff55532c32cb5ff6e29961965e7fb714cb0cb2d7fdb7a6586597bfcd8532c32cb6ff6e29961965bff3614cb0cb else 0xc86efbb6ecab264377dcb76559321bbfd5db4ec810ddfe6e1a764086eff36ad3b204377f8b569d9021bbfd5db0cc810ddfe6dd8664086eff16ec33204377f9b56199021bbfc5ab0cc810ddfeaeda564086eff370d2b204377f9b76959021bbfc5bb4ac810ddfeaed9764086eff36acbb204377f8b565d9021bbfd5db2ac810ddfe6dd9564086eff16ecab20434ffebb6949899b3feda953444cd9ff2d4a9a22669ffb6b5530d336fddb3aa98699afeed9d54c34cd9ff2ea8865666affb6f4432b334ffebb6a09599abff5d9304accd9ff6a09825666affb6e4c12b33777db52609599a7ff5db4e4accd9ff261a725666cffb504b92b336fedb86889599b7f7443444accdbfb6dda225666cffb70d3532bae7fcb869a995d73ff5db504b2eb9ff6d5a8259759ffd76d412cbae7fe996a0965d73ff553304b2eb5ff6d898259759ffb744c12cbad7fcb8658965d73fed432c4b2eb9ff6e6aa619759ff9735530cbae7fcb9aa9865d77eed9d54c32eb5ff6e6aa61975bfbb675530cbad7febb6a5865d73ff55352c32eb9ffaeca961975cffb6c54b0cbae7fdb52a5865d6bff5d952c32eb9ffaa8a961975affb754cb0cbae7fdbaa65865d6bfe5d532c32eb9ffaaa9961975affb6d4cb0cbacffcba659865d73fe5492cc32eb9ff2a5a5619759ff9735510cbad7febb6a4865d6bfedd532432eb9ff6ea9921975cffd554c90cbad7fdb6a64865d6bfe5cb0c432eb9ff6a58621975defb0cd290cbaf77e99694865d76fed3b4a432ebbf76e5a321975dfbd32d190cbaefdd9668c865d77eec3346432ebbf76d5a321975dfbb52d190cbaf7de9968c865d77eed2b46432ebbfe6e5a021975dff532d010cbaeff998680865d77fcdbb40432ebbfe659a021975dff30cd010cbaeff9b5680865d77fcd4b40432ebdfea65a021975dff34ed010cbaeff9a5680865d73ff5d953332eb9ff6e0a999975cff97054cccbae7fdb52a6665d6bfedc153332eb9ff6ea9999975affb714ccccbad7fdb6a66665d67fe5cb51332eb9ffa65a899975cffd32544ccbacffdb62a2665d6bfedc951332eb9ff2a4a899975affb6c4c4ccbacffcbaa22665d73fe54d11332eb5ff2e58699975cff952c34ccbaf6fdb8aa9961d7b7e5c554cb0ebdbfaeda865875edfd54d432c3af6feaa2a1961d7b7ed4150cb0eb9ff6e2aa65875cff9715532c3ad7fdb8aa9961d6bfe5c554cb0eb5ffaeda865875cffd54d432c3ad7febb2a1961d73ff55150cb0eb9ff6a0a865875eefb6a5432c3af7ddb32a1961d7bfad8950cb0ebdfe6c0a865875cffb735530c3aefddb3aa9861d6feed9d54c30eb9ffaeda961875affd76d4b0c3ae7feaa6a5861d7b7f5db2cc30ebdbfaa99661875edf970cb30c3ad7febb659861d73ff5532cc30eb9ffaeda921875affd76d490c3af7ddb36a4861d7bfcd) else (if i < 12 then 0x4592ab1fe6384c6198bbb14461ecc2e983ab0395ffabfb97d02f5b5e2cbc1d7612e7d5c5eb7856ce2d605a36b37d651ac675856b0715ebab925688abb554faa515418a6f94b829105172a1f541c27fc4f809dc939226d64cec98c52f1a59e4a8e93c1255a46648428f4d1b9a33745d28a49126a1ff437485f90a120fd418281cd01b9ff23f6c7de8f9f1f023d7a79e0f199dee3b2e7524e869cc8390670f8dfc9bb436cc6c84d651a73348067eccd6995f32466450c63187830665f94bd017492e1a5afcb38962c2bbc5664aa59506297051cca1293e027244d1097f92b124ea48788f1119d232e46448c5918522fe45e48b9916d22ce45848ad9155229e45248a1913d226e44c48959125223e4464889910d220e440487d90f521de43a487190dd21ae434486590c5217e42e485990ad214e428484d9095211e4224841907d20ee41c4835906520be4164829904d208e410481d9035205e40a4811901d202e404480590051ffe3fe47f98fed1fce3f847ed8fd51f9e3f247e18fbd1f6e3ec47d58fa51f3e3e647c98f8d1f0e3e047950edc1d0a39007020dc81b18358868e8cea195c31ec6168bdf17222ce85718a95147c27c04c8093911d6225041e87ef0f421d4c38286c90d1a196830a85e20b3a14d028084bc0900111020403c3070e0d2c18782d30540099011401ec037205f40a0810e01b6027c03180300054009000f0018002400300030000cffb4ed2d32c367fda66969961abfedb94b4cb0d9ff69ca5a6586cff94e52d32c357fdb62969961b3fed314b4cb0dddf694a5a6586efbb6cd1d32c377dda668e9961bbeedab474cb0ddf72d5a3a6586efbb4ad1d32c377dca568e9961bd7ed434d4cb0dbbf699a5a6586ddfb4c52d32c36fddb668e9961b7eedab474cb0dbf72d5a3a6586fdbb6cd1d32c36fdda668e9961bf6ed33474cb0dbf7695a3a6586dfb94ad1d32c34ffdb7aa99561b77edb554cab0dbf76ceaa65586dff3615532ac357fdb7a659561bbbedad32cab0ddf76ce9965586befb6b4cb2ac35fddb3a659561b3ff5532ecab0d5ff6de9925586efbb674c92ac35fddb3a649561a7ff5db4e4ab0d9ffa65a725586affd76cb92ac34ffdba25c9561bbbf4cb2a4ab0d9ff6e6aa618869ffb6b5530c436fddb3aa98621afeed9d54c310dddfaed8665486eef974c332a43777eaa6199521bbbedbb0cca90dddf2dd8665486eefb4ec332a43777ca76199521abff5db0cca90d9ff2e98665486cffd54c332a43777db56199521bbbe5ab0cca90dddf6e6aa65486befb6f5532a435f7ebb69d9521a7fedbd54ca90dd7faed9765486ebf974cbb2a4375feaa65d9521b3ff5532eca90dddf6d59765486eef96acbb2a4377debb6199321bbeedab0cc990ddf72d58664c86efbd76d2b264377ddb76959321bbee5bb4ac990ddf7aed9564 else (if i < 13 then 0x68bcc57972f2b5e50bc957912f1f5e38bc6578b2f135e20bc357852f075e08bc0577f2efb5df0bbd57792eef5dd8bba57732ee35dc0bb7576d2ed75da8bb457672ecb5d90bb157612ebf5d78bae575b2eb35d60bab57552ea75d48ba8574f2e9b5d30ba557492e8f5d18ba257432e835d00b9f573d2e775ce8b9c57372e6b5cd0b9957312e5f5cb8b96572b2e535ca0b9357252e475c88b90571f2e3b5c70b8d57192e2f5c58b8a57132e235c40b87570d2e175c28b8457072e0b5c10b8157012dff5bf8b7e56fb2df35be0b7b56f52de75bc8b7856ef2ddb5bb0b7556e92dcf5b98b7256e32dc35b80b6f56dd2db75b68b6c56d72dab5b50b6956d12d9f5b38b6656cb2d935b20b6356c52d875b08b6056bf2d7b5af0b5d56b92d6f5ad8b5a56b32d635ac0b5756ad2d575aa8b5456a72d4b5a90b5156a12d3f5a78b4e569b2d335a60b4b56952d275a48b48568f2d1b5a30b4556892d0f5a18b4256832d035a00b3f567d2cf759e8b3c56772ceb59d0b3956712cdf59b8b36566b2cd359a0b3356652cc75988b30565f2cbb5970b2d56592caf5958b2a56532ca35940b27564d2c975928b2456472c8b5910b2156412c7f58f8b1e563b2c7358e0b1b56352c6758c8b18562f2c5b58b0b1556292c4f5898b1256232c435880b0f561d2c375868b0c56172c2b5850b0956112c1f5838b06560b2c135820b0356052c075808b0055ff2bfb57f0afd55f92bef57d8afa55f32be357c0af755ed2bd757a8af455e72bcb5790af155e12bbf5778aee55db2bb35760aeb55d52ba75748ae855cf2b9b5730ae555c92b8f5718ae255c32b835700adf55bd2b7756e8adc55b72b6b56d0ad955b12b5f56b8ad655ab2b5356a0ad355a52b475688ad0559f2b3b5670acd55992b2f5658aca55932b235640ac7558d2b175628ac455872b0b5610ac155812aff55f8abe557b2af355e0abb55752ae755c8ab8556f2adb55b0ab555692acf5598ab255632ac35580aaf555d2ab75568aac55572aab5550aa955512a9f5538aa6554b2a935520aa355452a875508aa0553f2a7b54f0a9d55392a6f54d8a9a55332a6354c0a97552d2a5754a8a9215152a0c53caa70b4d4a98252ada4f5491e90ed1eaa35d45ca89b5103a14741c280ccfd49f8b3e267a6cf119d9939d670f4dd99b17351a67c4caa98a7303a5e4cb7296492ba2551ca55943327524bec93891e72272422c8098f891db6398c6da8d4f198a30a45b48af114aa28dc4df89231132203c3f887790dba194c2ed8551098e11841f48371061609bc1288233042a07dc0ad80bf0045fe1bf7e7e72fbd1f57be617c26f75decdbd447a22f331e363c1577b2ee75da7bb017578e9b9d14b9db731ae545c8638c77104e0d1bf337aa6ecadc81b6db6966cb4d855ae835946a8cd3e1a55345c681ccedd9b4b31b65acca else 0xcd35976b28d645ac7358b6b10d615ac1357f6af8d5e5abb35736ae0d5b5ab535676ac8d585aaf355b6ab0d555aa9354f6a98d525aa335436a80d4f5a9d35376a68d4c5a97352b6a50d495a91351f6a38d465a8b35136a20d435a8535076a08d405a7f34fb69f0d3d5a7934ef69d8d3a5a7334e369c0d375a6d34d769a8d345a6734cb6990d315a6134bf6978d2e5a5b34b36960d2b5a5534a76948d285a4f349b6930d255a49348f6918d225a4334836900d1f5a3d347768e8d1c5a37346b68d0d195a31345f68b8d165a2b345368a0d135a2534476888d105a1f343b6870d0d5a19342f6858d0a5a1334236840d075a0d34176828d045a07340b6810d015a0133ff67f8cfe59fb33f367e0cfb59f533e767c8cf859ef33db67b0cf559e933cf6798cf259e333c36780cef59dd33b76768cec59d733ab6750ce959d1339f6738ce659cb33936720ce359c533876708ce059bf337b66f0cdd59b9336f66d8cda59b3336366c0cd759ad335766a8cd459a7334b6690cd159a1333f6678cce599b33336660ccb599533276648cc8598f331b6630cc55989330f6618cc2598333036600cbf597d32f765e8cbc597732eb65d0cb9597132df65b8cb6596b32d365a0cb3596532c76588cb0595f32bb6570cad595932af6558caa595332a36540ca7594d32976528ca45947328b6510ca15941327f64f8c9e593b327364e0c9b5935326764c8c98592f325b64b0c955929324f6498c92592332436480c8f591d32376468c8c5917322b6450c895911321f6438c86590b32136420c83590532076408c8058ff31fb63f0c7d58f931ef63d8c7a58f331e363c0c7758ed31d763a8c7458e731cb6390c7158e131bf6378c6e58db31b36360c6b58d531a76348c6858cf319b6330c6558c9318f6318c6258c331836300c5f58bd317762e8c5c58b7316b62d0c5958b1315f62b8c5658ab315362a0c5358a531476288c50589f313b6270c4d5899312f6258c4a589331236240c47588d31176228c445887310b6210c41588130ff61f8c3e587b30f361e0c3b587530e761c8c38586f30db61b0c35586930cf6198c32586330c36180c2f585d30b76168c2c585730ab6150c295851309f6138c26584b30936120c23584530876108c20583f307b60f0c1d5839306f60d8c1a5833306360c0c17582d305760a8c145827304b6090c115821303f6078c0e581b30336060c0b581530276048c08580f301b6030c055809300f6018c02580330036000bff57fd2ff75fe8bfc57f72feb5fd0bf957f12fdf5fb8bf657eb2fd35fa0bf357e52fc75f88bf057df2fbb5f70bed57d92faf5f58bea57d32fa35f40be757cd2f975f28be457c72f8b5f10be157c12f7f5ef8bde57bb2f735ee0bdb57b52f675ec8bd857af2f5b5eb0bd557a92f4f5e98bd257a32f435e80bcf579d2f375e))) else (if i < 16 then (if i < 15 then 0x267721e70de3f17871341a1c673c3793c5e1c4d068711cb0de4f1f8713419dc277c3793c7e2c4d0e306793c5e1f04ce006793c7e2f0cd08f278fc3e095c00c06f93c7e2f0cfe4f1f87c04894db8cf1f93c5e1f04e74d23832068c399b0be3f1786bf218fc5e1f04a28f278fc5e1f009e714793c5e1f00ce614793c7e1f00ca614793c7e2f08c6614793c7e2f0f804f3f93c5e1f00a0673793c5e1f00a06730a3c9e3f0f80653793c7e1f00a065378fc3e01c8ca519f93c3e0140ca614793c7e2f08c6614793c7e2f08c66f1f8bc23918ca33f278bc22818cc3214793c7e118cde4f1f886e319451e4f1f8bc32c9fc9e3f1784933617c9e3f1785c130a3c9e3f0f825000000000000e965d2b3a5374a0e935d253a477488e905d1f3a3b7470e8d5d193a2f7458e8a5d133a237440e875d0d3a177428e845d073a0b7410e815d0139ff73f8e7e5cfb39f373e0e7b5cf539e773c8e785cef39db73b0e755ce939cf7398e725ce339c37380e6f5cdd39b77368e6c5cd739ab7350e695cd1399f7338e665ccb39937320e635cc539877308e605cbf397b72f0e5d5cb9396f72d8e5a5cb3396372c0e575cad395772a8e545ca7394b7290e515ca1393f7278e4e5c9b39337260e4b5c9539277248e485c8f391b7230e455c89390f7218e425c8339037200e3f5c7d38f771e8e3c5c7738eb71d0e395c7138df71b8e365c6b38d371a0e335c6538c77188e305c5f38bb7170e2d5c5938af7158e2a5c5338a37140e275c4d38977128e245c47388b7110e215c41387f70f8e1e5c3b387370e0e1b5c35386770c8e185c2f385b70b0e155c29384f7098e125c2338437080e0f5c1d38377068e0c5c17382b7050e095c11381f7038e065c0b38137020e035c0538077008e005bff37fb6ff0dfd5bf937ef6fd8dfa5bf337e36fc0df75bed37d76fa8df45be737cb6f90df15be137bf6f78dee5bdb37b36f60deb5bd537a76f48de85bcf379b6f30de55bc9378f6f18de25bc337836f00ddf5bbd37776ee8ddc5bb7376b6ed0dd95bb1375f6eb8dd65bab37536ea0dd35ba537476e88dd05b9f373b6e70dcd5b99372f6e58dca5b9337236e40dc75b8d37176e28dc45b87370b6e10dc15b8136ff6df8dbe5b7b36f36de0dbb5b7536e76dc8db85b6f36db6db0db55b6936cf6d98db25b6336c36d80daf5b5d36b76d68dac5b5736ab6d50da95b51369f6d38da65b4b36936d20da35b4536876d08da05b3f367b6cf0d9d5b39366f6cd8d9a5b3336636cc0d975b2d36576ca8d945b27364b6c90d915b21363f6c78d8e5b1b36336c60d8b5b1536276c48d885b0f361b6c30d855b09360f6c18d825b0336036c00d7f5afd35f76be8d7c5af735eb6bd0d795af135df6bb8d765aeb35d36ba0d735ae535c76b88d705adf35bb6b70d6d5ad935af6b58d6a5ad335a36b40d675a else 0x70978ec5e1f02326f278ec5e1f023260661f4d85f278fc5e1a01a06f278bc1e3f08a2803f93c7e2f0f801a0ca01a0703017c9e3f1787c00ca811a4d1e8545e0860e0753017c9e3f1787c14433c9e3f0f830ba69c2a8c63c998be4f1f8bc148200e0602f93c7e2f0f829c3e1499e3f1787c93e1f8d88f278bc3e09c1807f278bc3e0f18e0cc3e9b0be4f1787c74034180602f93c7e2f0f810f5793c7e2f08330f301d8be4f1f8bc3e023500d0411bc9e3f1787c107a41a46f278bc7e1f04e0863113c7e2f0f820f40218de4f1787c1139d8de4f144fc3e09811e4b1f87c5e09810c6f278fc3e0894ec6f258bc7e1f04c0863107c9e3f17820f4023c9e3b0f8bc130218de4f1f8bc3119d8de4f178fc3609811e4f1f8623e29bc8e2f0e17c7e0981985f0f93c7e29a1985f0923c9e3f04fe4f084f0d85f17827f23870de3c2f8bc13e1bc9e1f1e1423e29c1a0c03793c5e1f1f810e4e9b49a3d0e811c08c3d0e4f178c8fe0f0cc08f278bc647f0f82704793c4e323f87c13823c8e2f191fc3e09c11e4f178c8fe1704e6dc678fc5e0f278670461f0ba4d1f87c10ca30e66f278fc5e144ce0d03617c9e3f1787c107a41a0662f93c7e2f0f810e4f93c5e1f061e5868a3c9e3f17878b381c0de4f1f8bc3e0a2d0390399bc7e2f0f8221419b0be2f0f83c7321c103998c66130789206820cc051218cc461301a08f061749e3f17850f39984985f1f8bc3e083d185f1f8bc3e0839a270681b0be4f1f8bc3e08392e6f1783c9e3c2cd88c3f1b89c2e0f038b402389c3e17078007a2d008e270b83c009f1670471b89c2e0f0026c5a011c4e1f078012e2ce08e371387c1e00498a471b87c1e006425c59c2608e371383c00971680471387c2e08478b38238dc4e1f0b821162d1c6e1f0b821908f167098238dc4e170423c5a02408e371387c108f148e371387c20b8478b38230f86e270f85c1e2d1e124517c9e3f14c0d0381bc9e3f1787c145a7c9e3f17868b279b4c48a2f93c7e2f0ce00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000188c39da1866f278bc3e0a7118786793c7e1f01ae8c461ce90c33793c7e2f0d3e4f1f8bc3e08441e7f278bc3e08444e684793c7e2f0c466f278fc5e1844466f278bc3e0902728a3f93c5e1f04fe431f8bc3e09451e4f1787c1139bc9e3f1786232b8cf186c2f93c5e1f050e13be1b0be4f1f8bc141a1c186c2f93c7e2f0d10c94117c9e3f1787c0c6a46728b1b198be4f1787c14d8262c662f93c7e2f0d031945818cc5f278fc5e1a4d067c3617c9e2f0f8283419c988f42e1bc9e2f0f82ac7b80d071c3617c9e2f0d26833e1bc9e3f1785134134d06743793c7e2f0e2693419c9986f278fc5e144d) else (if i < 17 then 0x8f1f93c5e188cd08f278fc5e188b9a7041984007f278fc5e132d328a3f93c5e1f04d28e371788c3e1707818727c5e183f8fc12c1fc9e2f1f87c0a51c1ce643c97c9e1f1f828068300c05f278fc5e1f041cac461fc9e2f0f826228a3c7e4f1787c027a1c108e067e4f1787c130218cc509f93c5e1f0502813d8fc9e2f0f827630a3c9e2f0f806739821040c7c9e3f17866043198a11f278fc5e1a18be3f0d83c9e218ce28f1f93c5e118ccc51478fc9e2f08c67630a3c7e4f1784633f8fc5e11c8c65198a3c9e2f08c661478c65e4f08c66f1f93c43718ca0d06793c7e2f0f800f46801d043a087c109a30d85f278fc5e1f05186c2f93c3e3f1780d141a30d85f278fc5e1f0500602990c66230980d1461bc9e3f1787c0689f0d85f278bc3e0344f86c2f93c7e2f01a27c3617c9e3f1784d1381f0de4f1f8bc3e0c2d07871e1bc9e2f0f830b461bc9e3f178115361bc9e3f17851330200ec6f278fc5e1f03169f278bc3e0e2cb46a2f93c7e2f0f827842a04f46f278fc5e1f0516a0401e8d45f278fc5e1f05346f278bc3e0a2cd46f278fc5e1a2cc0602a9146a250a815143188be4f1f8bc3e013d027f278fc5e1f031a71409fc9e3f1787c145a18de4f1f8bc3e013cec6628e3c9e2f0f806743198be4b1f8bc3e013d1e4f1787c02762ccc662f93c5e1f009e714793c5e1f00cd8b3b1bc9e3f178492319d8cc5f278fc5e1b00a2863317c9e3f1786c027a3c9e3f17844ec5998cc5f278fc5e193ce28f278fc5e118f16763317c9e3f17844f38a3c9e3f178462c59fc7e2f08e463c5986628f278bc231e2ce3214793c7e118f167f278fc43718f16693b1bc9e1f1f8bc0c5a00c055228d44a15029c853d1a8be4f0f8fc5e0a14f46f2787c7e2f051680329146a250a800aa7200f46a2f93c3e3f17805148180aa451a8942a013d146a2f93c3e3f17815141a30de4f1787c10f9f0de4f0f8bc10f344e6833f93c5e1f04c0f3419f0d85f278bc3e0a70d85f278bc3e09b0de4f1787c08f99c10f93c3e2f023e534018c862309801e67a30de4f1787c08f9b0d85f278bc3e033cf86f278bc3e033cd86c2f93c5e133cde084d006311811fe4f099c803190c4613003cce3e1b0be4f0f8bc0689f410818c8633118412681f0de2c4f93c7e133ce6833e1bc9e3f17871341a00c6431988c20933d186c2f93c7e2f099e7f278fc5e1c499e644e1bc9e3f1784cf3e1bc7e2f0e24cf361bc9e2f0e24cf361bc9e3f0e24cf361bc9e3f1624cf3682103190c66230824ce3e1bc9e1f1f8b12689e18e663f8bc9e3f0f16863b998be4f1f8bc3600652c773233c9e3f0f809d42318ec58478fc3e0f2508cf2787c7e0b139a7843998be4f0f8ec5e0a0248cf1f87c1e43131e80931dccc57218bc7e1f0232ac3e9b0aa0f278fc5e10652c5f278fc3e0464ce672189c7e1f023 else (if i < 18 then 0x23f80232f93c5e1f038e632f93c6e2f0f82673395c8e129f8bc0c821ccc863f93c5e1f04fe4f1787c0e595cce57218dc4e17032086431dcce5f258fc5e1f053e4f1787c0e597c9e2f0f83c72f8bc0c8b1c9e4f1787c163974be471f8bc3e099c1a5f278bc3e39b4c2ff278bc3e09bc9e2f0f834b2834180602f93c7e2f0a1fc15793c5e1f061e5061984b07f278fc5e1f05266f278fc5e1f0096752c266f278bc3e0c3cde4f1f87c06bc3cc66f278fc5e1c3cd0883f93c7e2f0f8270401ccde4f1f8bc3e052d2081301fc9e3f1787c0a5a61107f1f93c5e1f04f0883f93c7e2f0f814b4198cbe4f1787c1139c5e0833793c5e1f044e8f278bc3e00c04ccc65a010077328fc9e2f0f80cb4c220fa3f278bc3e09e11e4f1787c113734e083308c0fe4f1787c065a4680832f93c7e2f0c46832f8bc311f1f92633197c9e3f17862338a41066f278fc5e188d066f278fc511f0cde4f1f8bc2660899670401dcaa0f278fc5e133530883f8fc9e2f0e82784793c7e2f0c45cb3820ca2003f93c7e2f099a90401dcca0f278fc5e132d30 else 0x0)))))
def lay61r10 : Packing := (1776,4,5,63,0,15,1,word61r10)
def keys61k11 (i : Nat) : Nat := (if i < 3 then (if i < 1 then 0xc2260292f390e2b4968c4dd60a2e19e0cc8a04de527ec8bd5f96fa47ca0e6a2752fb02e48bc055689744da8e541931558c7762d4c29cd87d4484313bcc1c1d2339075362452ae2e179b04a8a335e398a377b836b47c34623e2ffe89d909c143f562d9f87f6e14581528244010041c01808020a028d00a2c000000001078000a030001422000c01400000980410080c8000c030f86800084201cf0490903cba021a01c06001903c020000004000a0580c065c0088c3406090004c2b002b8000b060005c3f018002e1e008005000028204c0f1c8000006080c00a1311878ba0200028060000100340108000000600360241f0c89006230310c1e0203824000c008301801050082a40048000000010004407000000a2702048062a06a746c042d85026000202c12000203008100489c020400024040108808803c0902cd400130e014170183848070402016000a874160000078004700008160a02844000e06000c6020481c020806878000001804461103810463903148768d120140e2a00000400033000100a0000c241300068200d0008c4800019b00802308000a170200004281f8840e0e0300402000300c020a000080804078001408008244409158480013009040ecc0408c0a01020540400058000000030041800048581a28040000603000009208010004029010401e000881c0c9b0481402100c019208e198000000000003a000180c52020081c0e1a3c8100200048001e3c0a8001467010002c060989402001a8411e3f01808021312804f205030301001080283400054380003058181c2b000c80c4c0e0002e020504c064f0080c06030083006000180006020304800070c9401a262800008a10009c4e090207c7c0000828000602804020104040940f0000400020700000380600000000000c2a01042a40817020100001028580a005380c06380180c020000004180f0386c06041b0007a0302090680501850143c0280000000f04000470f01c04001880c3449038001605048185006008080030060340c230b1f000000b04c06021300c0e064900c0e070d0441007010081a0100018bc01028701c4f03800d4001601c000f2689c0000108200c07008c800010102c0800029782621008041200008000603050000e02020081e000a8b84e2f2387412000280c2c00000040414021a80683000000a020c3986e08078641020028bc1604018080010008000a170587c02010c06c100c130e4005e011d83a0c0387950240305c32030c00034000005c00071009c0a040205400005e820040f1700c020d000080c002d00c0200000680016000ac0800028081009010c01a020980c0c0d11818045a00898120819804060007014021200800ca26038086600049cc040b0200018001281002482b0b00006050680e0100000083300814001600038041e else (if i < 2 then 0xc8910e4784835182461f38b475763e6090e730b38a5883edf24e80000cb05c41972a0702044040231ad02400001a311c525ba1c1240dc390c18e1413a0513c40a000008e880002cb41c0af641d8090842bf23e3232e9819a8b3de14e6060a954b20b5080f1483292be0aaa2df1000059738000084be5003000015b3cc810000000000c4700000831480002e74c8823b1f9800000001462e0000784c2c70165c2501e1753284ff608300001923986f0000089070000006f206ec0000595a103c5f478000050c160551a66ea06a804d88a8ae47291a5f4f1b0862c32892fccf0ab46580000e31b7977a87ede468d5157b3ad129820ea8088e93bfccb8608800001d924dbf602646d62b97ea30514080000030e864630a2f174d3376a68036920810b3f16578939819d35651a03ac2980354f0b6eec2407c9054d113d88a0a8811ccdc32c5a4172460c06846d0ba8b708d6505f1a2d36eac35464c0fec462f8c54c2d7849f24d298fdec5609578708089ba5065441e350d9d13c6451aa9a7c1ba88de8c3d388dfe0ca28b873af025f32375d4b7ac6c8e6b622777a4b7d13d618d13627e3f7022dc15d90834863f89028290b327a86170c3b2039801831246063c4b4bb1067b4f48cb1857e42243079000009ad028bf099dc931aae0968e9631208c90e0f2f32d615408507e89cb892d98c409e00000e36f80003e59d1683e0b111a3146600480205ef007bd89da01172f13165fc0ff64ccf017fa7694047c62d824805a2d4b888af9989888391083bcbe34191adb7285f52ad9e30000003896b1156436310be743b59a2c61642bb67891a0000881f0000092a40551ab0dd8c9cc46305d392694d998000000d16302c8bedcab94848220c0000288b9a5e4020519a7eec12000042725db60876796b9f2de00000e029446a22ec000010d778034700ccf2edf48343926096c1b42484600008023f8a2800000000c310000000001e991336af93f800012ce6101d9803782fd2ad62864684de0a76a2b3dc9b505de0d448660bb5580b9065e186a1e172f2147009a265462dc8140a4cf82336715e50ffa7364e3443d83d062d0530a30338d49856e48f52164725b88041e28361c660bde800060ad923c88e07c1778a2e486b236e70e12171ea6aac2bcb0e3f5ac9c39fd28c04b6c5b6e0223b17978fb8028eb4b7c19cc8580c9c761c0e72ef27710b6245b21173782cf058381cbe8c4c8fc682ae65a7d065204340737627e70fbf003ad06545894c80de0ab0db5d103434c9c5280cf2f23f004d21347604f8280e96b9b3b50009008575c6985cc03b2a38da02f4c7cdccb3a5cf08b6c91549c5e008200ebd94558cac6644d1387cb3608de82ba213ce016d8b3565a1db6b84b2fa466203264e978763044cd05445a4c8350c1af022800f53a9d4cb7a84bc45c52074342 else 0xb16b000000000000042570000615380bf60000000000000000000001689f25400001eee6000050a4b093400000000797f60d070396613700000c1e60453000000003644960b0000028b9c00000000ad85792c3241904a600005cbc403fec23624b21c5ef0ca16155318b00001c03e6193000010224c66321a1f8c980000c7f944d8000049a280000524a120d001c3068c0000a2b8000018bae041f61cd0000000000000e01410fd00001e471e081119edc7d00000151cdd2a359bcc5e0aa1f0000390978153f0158000149a8050ed35ed133f87de0175706e94bbdc5e8c3137176d977241fe6bb0f468df2da1a3fe6bed2fc2100d24625453100ae19a3d777119cb0450000085a885baea514e42c32d9c4606d74f09e3132904260295a10b011a7a1c382c562b748b49e2bf71aad936b0d6ec067a09180efd834c82e96052424e500e34c3589313a0c66093e0188c81e88101bfc03a0530a80009f20cc3a27c13ec77db06cf4b804eee91ce412c82014806e128280992307276d990af526ce971b0c2098f7c6b8702ff24159b5b0093886d581e1c4d8c671406d32b618db50896a94a82716972f002f2626c8e3611a7cd41a0f841ec891db69fbd6d0832aa24060275607eb0f9607bf0995a60162b5ea382480df012e0a7a0ac710981531615db1810817c30327249596dad183b95492318999502b90211ba304a2ee5441a0f561cba8f0e0d21bb0d710da8053d490428e12e64847a0bd1e139301f40243c8ea4222bcedb2e220a535b24a508844f80000cd10f509f00c6509531ca710950264467803197025181940000000020092ad5c4086c68515674a87bc1b60000718700000000000000000000034522c5c8a1a7800008c980000001e800000001e422ae5c000038285215000000000145b4000000000000080f903ce00001981c000000006a7c0000082c6c1720000000000001c5873371f92610613921a0000309d32098c4a400006397c002cf1c1000000002479a000060038c8bd92cff4446a2680003ea0c0000529500000000000000144800018ba5c2970000051080001b926f2dfd44050a13211c21dbe08d7005c86e8d1eb4142d075ba3ebf925c0a5330571527434d31b3e8b4ac284b36528527d68aa8c0c22ed1310c00a464e9454895e197d8c36e0000086b0818f0686d2ed793200000883000000000216dc2842b2078000080b342995809f0a9d4bbe0000335422d018003c5ef3eac8925cd9d40000e10300dc406b60000000009b0a8ac6442700000947c09623153000030b240000a0b500006206a417882c7b2751368f03e0481166b4c8a8b8bca00006265e871c0000b4615253c963d4665e15e85b14b11082e3453211c4e89bfa8d3f0cee34be9309525e9d086706bc0760cd97559ce9a14059480b74e200004996e050282dec0a)) else (if i < 5 then (if i < 4 then 0x36b02ccc2fdab10c1117b4427800000000000000000c2724360c19cef9ce93e400003983101b0e5e679b6d8be181da627cd161f33d449be00000000606e000018507cd91502a2c603a1e5b10a1c8888588000021ab7515e32d4454bc5a9b944ba9d4837488d63498c00006691c1339037f0749e1b40243b9a4f16c1e2ec00002d1614d79b25d7311000035a1200005929800000001e45e5568643e0000000009c9140f6a24370698d881604321154e524d319694f803cee64290f3080a5160691f59908f9613dad070ba0329916de209502bd61328e0b20894b36e033551a9ff64b0506321bb16d38c16a36a3359c18ac2d9bc8d5d092583ef16a3713da290c92e4b25145aeb6902a29cca40f8a489039128616fc44ce12c6c8e0d13d066800a8e2252e81e1406001bfb13cf89c3f4459052f377ed84e414b82e00d1b8632556ac793a482d2f95fc5990000647d9dbde54760358d02cb62a11aa4402acce46936af6ad01a1026008b0043531d0b387ece72f206c000062b5457672ed5151ee9045cd47c2a16a55b5b2ee2b345c933619c511e321223c000020d040000c30ac0cc0395aa8c60000f1b131b840000ecb042fe30d17fafc266daa7dbb99c00006af749c3206fb1057455638f2800000001a24400000000388a200000000000028850000000000199c0c38a146f17100000ac32c4bd5526203e437a5f6ee720700002486ca5be228d85175eaed3b0c022d8041c00016a17cb7071753a8da00009104000030a69668e810785a368d59fd765a2b12d680001268100cd0843d8049c3f99590715c51070e416e24f04e2783894a0fe0c92b2d00000403800000d1e74ce514ac22e358cd1d5afe424d049ae4a86aada33bf33aeb11dc0df1c2fb1e2fad774a333cc63154dd2aac726c61fc2b962761aaba81b9784120724c25780ef2815a821acb4491e70149807d3baba062ce161350e784a0e5ad5210a2215065d6464771ba9115d3d56387022a390b5a2e3014a81ef7412efab146038188015d129537e405048a8c478dce7558a264e0ad1495be11d51c4586b40000b02110bcc0645936366dbfebe1b3c846388badb09fa46154ae7469c50c638f9e452b26e2a061000014b39451ac07448594c8a50537426989006631e038586bc99124bafba3bcc24359b38a8bf65f422eb7ac140000000000005b12729ea217a22eeb91964517b1f48155c52d86dd369f800000178e022abd0aeb6fc0607890a85f07238611de4bd705ac82bddf31c409cd57a733ec0310ad19c3a8022319aa616c344b6b08f99741432cc5030000339d0c2200000a14ec311906d963c0114b09ba8c732a13d0000795dfbaf4656f115add457a79000000000414bd4a3a00005061a05b80000000020c01919b4d4c840d732300003b98ab65cc5c5d0e2c0000a3637e5480000000 else 0x46110000682a7d9f80000a364000034be4863ed904be2ee0a29a10951389d10f01360000818978cfc0537c28584c080002c63680084a6ef84c844db005800000159245dde51622a52d3ac000083a300007b1018868a2ae8516f8ddd843306e620758d12363dcc4b30000582b5c89c04830000108540001a23e536cdcc3f0258a129f20f104f98404213b3d879122bcd5f440c3012f2ed2ea5e0000e27e1c3e70b119cdf5b5800000000046adb4de93b6800000000b1d62a33e015629026293874e8120945f580f6589077a93e12051c1682b8d48361a3a85540b3e0839d446342d200b586ba016f2463c883540ede262f369998c36c316640b2e3c8f8908bea968c2dad82870b3a4195c344da76f9216628c3280a84cc858c0000d1be2044c000000000078b18840001023f90e5420fc0001019bb19688a9881980a3f00005a0d883f1250cb10021ae9975f40e1e36649b274d9ae526633f7db940001303446fe000021333d4f90000286800000c19900000000000000000d2dde0f55438a0000000071ad3c6c20000d677125500000a1ba72ec915831033a045291b80003932a0000f2317e6c7477180bad05cf21ab0c3c4e8a4671212ed48268255812480001486ae47fb2a2486ed85aeb4e9a23f0bba9d0ea000071e63862243fdc35e000078cce140c0000a2007ab4d61f8c08bc29c596a960a1a625a9249105e8571e511119d7abaa80d7e1ae6c93819eb887ce2750000000036140a19c11dee1508084b63ea0000507e9877324e7b345c04d2569ca2ad1777384208a1e239dd175783a681f8cc36e19f38ee9e9c063141b6729904cdca24a3f20a4227ccaf8784f415b81585c69c646ee2945156ac62ffce0fa6cb0cddca8ea5c342b11b4e504b09466210f0c11ae35fe021c20908bafdbc4fce680801e55943e64924e32902cf8e4b7e3c19b548930c28b381fcd30d5875541fbc49602016027f53aba64321b3e0e9ac44343b031187159486b200001a31053d3914b40ece007e14c740c984d52319f2c25288e552c395c91a6d84b7351e52c9892e9075545498043d47b3077d42ac1047591ae4809e3e00123a19a481968be200200033c02d04420636c597b9cd2c055e72af80000000021ed52d83393a4b3e63cf4131e3b9d4933639c60d1317f9cab3c4aed864c18de44e7d2430000000035af08558302ba97a580340000730c000000000000000000000081240000000021a2329ffe4fb3313cb2df8c25210b93318000088e803fbb07bc48ee807fe29a601b00000000113c911301d0f40000e6c5791e80002969e000094415837ba386a52240f8c44025855a07be8fe489ebc76266570000397b08b28253a42bb000034c1d235fd2c1982800000e3730b6964c34a8b4000000004ec23e44f796d8252e166342a84a4d95bb794b8054600000000) else (if i < 6 then 0x8a1f07e40000417400002cbef42b230c18000000001da83376a04bc8c200000704e9d379c0f36ad1f13bdc8d4000061560289a3a2fa15ca666db297248832d6860a8532101b906180000d45327824361d01a84819e32d9a4d35254c0db21867559fc2be985668a79c54043d4c105219c1aca390a8c3415122706fac55df2bfd18d4187f8caf317f8000224aa000092286091a4cbd464a403c5228c4ce2000021db581a920b312757a1a0000302d40000623d800019058e928a279294cfd0d171428347800028ad3a06800001c7e00c72e90500005b4100001d830692780000000000038515b2d4947fbb2514112b082f0b2c0187a0db924c6c4d7008cb27be9a54e5be59004918785b0804c23f08042333a2cc49c061390f1164ac017236902a1e20570d7362fe3011118e90a9805ea21fd5065e8bc39aa55b63b11b0e1c189b0b5b85e38182349d10d0640a8595690625ec910f1b4b00ace1b291eba034f604d63046249eab6e04b8e4323147998ec822f28fb130bb0dbf8ab705ca132ffe03ed7199510833ff835921fa36e42ec579471c75c864b634a49ac000bf1308b2a451a48d8a9c10380b308271837ee069d082e8a92d5972151211a5c7e8c816d904d25c7cec8c68fa3529b6548b2e03995273405b389640b46f23e534e80f4ec2d32131b6f710dc8802693a0a27d060f1d26bc32bf1d498ad9f20483dfb5823831a4909a4f529303434d13192370a0511153c005429cfa30d989850617c121a49538ed1167b41a4406810cf600a5e1ceb8867056137d8081411f48936c491f809e91c6219acc4488035016cd0e78055f8233817e914da64d840d93066e83d36216e1894004815ba49ac36a8c0934029b4643c27da21d4069c83acc0bb48b62154ccbaa69974307a86974937a027a81b201cf0c9aeee90720704d750250b6f0a7d48d0fc6d793cb6108407d741f4d26a20be4104280e4e98aa5c3b90e69bcfa118a25fc848b0b1c044fd927292cb074f106c31048c550c16e90bbce6680314411a5a29a10e81992466ba03aa07706861ec75d1aaa33b00000172800000000448bb8066000041fc61304000020b850518000005b600001016280dfb8920000b04a09b788652c5f661c750f6fc2ec1d89f06e78c7c4c0c4d74e1e548d5e0876861453577488f20a514f17b71840a8825165048b6658b605b71a6aba272987e7568271f96de8d0b4a64ede368a16e987aecb3683c861e8098bea1a2000081ac7148f02b46429e769d1255548130d99134c095895c12634235221185a3fd11f14171a16160d81843c85a530d2a408221bcc36b80001172136e2f0876654cacf06140609c10e438dc8c302267a0ad0b87b1c557423ce0a184a7f6d77a92d00000488200001893613665c5889d384f0193e483a788ff4352a93420314b05855a8414c18885 else 0x2c359972340ce703110d241b4d1950127a52c238476ab95c22670f750aa9417d168a405e2e43ae5d18964490e211fa282504e8a15d479e530a9dc82da49d189959b01073998e3cb8b2063e0e884743480e847d613420e44cad5c4f6331e2ab704a8ce174d08d9b3b0a74f20a7a072b95ea82e0a0b1c614ead304c2cb02cd570b82b24bb60000000e60ffec699712c302248f12564505af00003982719cf51c2e6f2e93fd828720e2f11d513e0078e4190229ab85fda2518381d23c3db0e12ac869e992f80000a3780000928f68300000173e5720a800000000702dd04b80001069b02df000051bb800a70227500ef61f8adbb0acc00000042b0644000000005823fc6b40000489988453c510d0a7321ef0872a752e6e0503ee0968c76b6a1ffa329803101c6a104331fd9a344b71858cdd859a13c440740951cb888118425c00e0426028ded99e6b00b00a0ddbb34a1ac6b500003802bd4368119e1805016b85c0c6ddf343a19bc0000ae89d838103250225c5c1c24a00002061b21f60000000000000c651000070cbf0b9bf8fe00003083800000000303d00000c7b9ab4d61b349440b10b8340f093d991f4a0a000000c328784e861e0bf000038e961269e52d0d9368ebc029ae25f00005142001ccd528929cf182081eda43f82c89268f8adaa30854615984c4c5103484414cc4a40001924089296ab96f9bc205dce74d9ae34866c12538ea31370a0a765905924548e38d7e641b50cf00bd9cacc653d04b48161b8a00c237516560c3f65f8000073317c6ad448a405c7365e2441e269c074f76f483494c1ae2aa2368b471409ae81cf115299925c13004092133693b7ec814b0606bb4b0bacacec365903bd593002900000729e2067f96f1e8a40420589b352cde29f00006)))
def cut61k10p0 (i : Nat) : Nat := 0x984c26130984c2613
def face61k10p66 (i : Nat) : Nat := 0x19903060079c03101e71844659c35581e7328e649c0f381e7078460c00c1006203ce5f2095419081ad063acc6518b0311661cc325184a306007206b401660744018803101e70744310837486e90dd26024bf580622f904aa01d103a2
def cut61k10p115 (i : Nat) : Nat := 0x130983426130984c26130004c26130984c260d068341a1309864320b05848160b0585426130984c2613098380013
def face61k10p408 (i : Nat) : Nat := 0x78451001d10c420744230446088c111820c041d11a0000c401881e1144021c400002d08000000052009d81a5034a068b803100001f825100a4012e11f820f085710fc128802984d00144028805100a200bc433405100cd009ee25c24b8497092e125c24b84cd01a0033404494cf719c0334051001d10b45
def face61k10p472 (i : Nat) : Nat := 0xb4205045e20bc4178844148828b45074444148828b45074443885a28b4529000000680944028805100a20144028803a807500ea02880030cd718a8e35826a84d4189ee1d821c8c1918b6e34d05200a400ea033406700a20144000005100000156207440e881d103a200c40e881d1006200c401885a298b0
def face61k10p536 (i : Nat) : Nat := 0x282048c5c20fc129005200a40148029004b84a4012e11d4068b8a401a2e33406700d000fe1290027b87500fe125c24b8497092e114c25100a2019ee11c651002d083a2220a0e885a29105168a2d148710b4507442d145a28062074444145a283a22900168488285a102822d1488285a1168a4b848710a61
def face61k10p600 (i : Nat) : Nat := 0x29005200a400ca229000000000018236dc6d0cc181480290052006510ea036466c8c03110e200c452002d08bc428801684a201440288051002d09440288052005a285a10b425100a400bc428801684a200ea01d4052005e2148017882f10a200a8e0b42298453085a114c22f105308a61360229840918123
def face61k10p664 (i : Nat) : Nat := 0x22dc30886110c22381c70906110c2227dc4fb875003a2074470381e11be007446f3c0c1148000000608000148019445200db70ca219440000a4014ee1d402304460806221c44388871006222dc45b88a7116e22dc45b88b7116e374045b88b7116e05c432880c11b4337045200000000003045200a401480
def face61k10p728 (i : Nat) : Nat := 0x28805100a2003c2340027b8c180c9039c27104e471cc338827238e209c8e3882728cb019c8e38827238d001a0034006700e31116e07440e881d108c107444388ab11c41388248208d203a207440e88df011c407440e888618000151c5500aa015402a804fb89f713ee18444fb88b717602ec05d80e0719ee
def face61k10p792 (i : Nat) : Nat := 0x2186430ced410c3154676208618aa315464820eb410c321863088861890106025c0c5471d482186430c1c18aa33a9066408618441306011045b7164e06020c0422098b006025100a20144028807038e919c0e19440f081e103c207840f081e103c238820f08e8003c238827104e208ae207845100ad7158e
def face61k10p856 (i : Nat) : Nat := 0x23487820e209c41241048201d11208241048206110c2218440e888d20901118200009041d233bc6000082118b0000050bc0000000000000000000a8e16dc018803103a200c400000c1006207440e88ee110c33320430c54709ee13dc66404f710c313dc2a385470a8e2a805c0c54716a116dc430cec410c3
def face61k10p920 (i : Nat) : Nat := 0x7920f100c6818d0493c9278a8e151c550097095402a801684d718a8e151c2a385b70b6e16dc2db85b711a42410438846088c10bc423040310062
def cut61k10p951 (i : Nat) : Nat := 0x68341a0d068341a0d0683412190c86432130d82c360b0906424120a82c160b0582c160b0582c160b0582c160b0586030100804016100804c26130984c26130984c260e070002615
def cut61k10p1015 (i : Nat) : Nat := 0x130984c26130984c26130984c1a130984c26130104c26130984c26130984c00130984c26130984c000d068341a0d068341a0d
def cut61k10p1060 (i : Nat) : Nat := 0x3d9ecf67b3db00fc7e3f30976cf611fc488040201a0804020100804020100883d9ecf67b3fa010080401ecf6241207d0080400919cc24023900bd400910024403023c8067200be80
def cut61k10p1124 (i : Nat) : Nat := 0x4020100803d9ecf67b3d9ecf67b3d9ecf67b3d9ecf67b3d9ee3a7b3d9ecf67b3d9ed9e7b3d9ecf67b3dc790080400911d0940474811e40201008040201008040201008743a1cf67b
def cut61k10p1188 (i : Nat) : Nat := 0x50b713aed753a9dce974cce088040201008040201011e40200f680402010080401ecf68040201008040201008012200488e11c75002440200488040201002410b3c487f402010024
def cut61k10p1252 (i : Nat) : Nat := 0x401c28680540f550249c4ca69339fcaa08241e89201045b090709d81410702499981b70381c0cd06857abd5eaf6db6da8ef912bd5eaf6d974d0de6db81b33f6e2a282dc6e3add69d
def cut61k10p1316 (i : Nat) : Nat := 0x4020100707b201badd7d375d8dc402a100e76e379b29d403e1b6e372b6db6f86db95b7147db7dd0df7b365c4e46cc09b2f66cb91b3026b4cd00d6544ce66809c2c6633358ccc4880
def cut61k10p1380 (i : Nat) : Nat := 0x6da753a9d402753a9b73201b8806e20100883db71c0dc6cb65b2d940200488040201008038411011740202042450c10b2b370d1c488040200e0f97b0f500e06e2013a386ca750059
def cut61k10p1444 (i : Nat) : Nat := 0x1188c46361f9f68c7d3e8a854454020100bd37af4def67b4aa86804037100a878c0db6df804bde52f3dc01bead7cb99b8dc6e3993a8040200e0f97b371b8804ed0266e240371b703
def cut61k10p1508 (i : Nat) : Nat := 0x1234100d0202004880441ecf67f1208e8ed0685208747401028080401ecfe274009100804021cf67e4009048401209048801209048431389c4e802010089203d9ee407b3d9ecf67b
def cut61k10p1572 (i : Nat) : Nat := 0x40201011e4028500a850a0100804020100a151a1c489e89a793c234f1ec46a06928180a050135407e500b1a62412090488018c78491e402844824230904824200984cd0210990024
def cut61k10p1636 (i : Nat) : Nat := 0x1188d80c0603023a7d3ea9cfb0d26130987d4f9f5802a1530848241208e3a241230848241208e3ca11208442214020100ab12200488050a013a2412090468ea3a007080402b10024
def cut61k10p1700 (i : Nat) : Nat := 0x1188c4a26134763b4712c744b1da3a01007b382b0783c5551d008e11c7500241220154241208e3a5942a150a85512144880402a50a8543a1d00241230900a242c754c7b2888c46c1
def cut61k10p1764 (i : Nat) : Nat := 0x1209048241250048231188c4623
def word61r11 (i : Nat) : Nat := (if i < 4 then (if i < 2 then (if i < 1 then 0xb7dd9564c86dfe69d9021b7f98664086dfe6959021b7f99764086dfe6559021b6fd9826266ebf6a68899bafca9a2266bbf2a19599aefda8256669ff6949899aefda626266ebf69a8899bafca6a22669ff2a68899aefda6a2266bbfaa98699aefca961a66ebfa218699bafe8821a66bfb6889599a7fda6a65759ff6a0965d67fca9619759ff6a4865d6f7da521975bf768c865d6ff9a0219759ff2a6665d76feaa65875dbf6a1961d76fca8658759ffaa9961d67fda961875dbf659861d67fda921875dbf658861d6f7da521875bf768c861d6ff9a021875dbf662661d73fd9899875dbf65a661d77dda664c75df7619931d77dc8664c75df7999931d77fa8864075dfe619901d77f88664075dfe999901d67fda8a65659ff69e9959777da5a6565dfe68299596ff9a0a65659ffaa9985967fda726165bfb688985973fca9a2165edf296885967fca9a21659ffaa997596ff5a125d659ff6a5875967fca961d65b7f69c86596fbda421965bf768c86596feda221965bfd68486596ff9a021965dbf2626659777ca961565ddfa6585597e7ca661565f9f5d9855967fda9615659ff2a585596efca6615659ff6a5755967feaa660659ff699981973fd98a20659ffaa9971967fda961c65cff661871975fd9761c659ff6a4871976fd9899865ddf661651977bda865065defa21941977bda765065def61d941977bc8765065def619941977bd7665065bdf69897956f7da825a55fdd68496956f7eaa61a55bdf2a586956f7eaa21a55ddf6a486956f7ca921a55f5f69c86957f5da321a55fdb68886957f79a021a55bdf2a576956f7ca85da55f9f25976956f7da81da55f9f6a266956f7da899a55bdf2a266957e7d8699a559ff2a6779567fda825a559ff69c969567fca961a55b7f69c86956f7da521a55bf768c86956feda221a55bfe680869567fca95da55dbf25976956f7da51da55bfd684769567fca999a55bdf69666956f7ca65d655bdfaa965956f7da859655bdf2a165957e7d7659655abfaa98621b2fe9961886e9f6199521badd8664c86ebe6199021b2fd9826266d9f6549599ad7eaa5d475f1f999751d6e7ca661565b9faa965197a7e8859465e9f61886957c7d761da55e9fa22669567dda3a65869dfaa99521b57d97654869f7aa99321b6dd8664c86dd76559321a7faaa64086cfe6199021b5f99764086dde6559021b7b99464086df664d9021b7e99264086dfc6459021aeeda225666b9f6948699aedda321a66bbd6848699aef9a021a669bfaa9961d66fda999875cbf662661d67deaa64c75db7999931d73fa8864075dbe999901d67f9a0a65659fb6889859677ca9615659efaa9941973be8865065daf99994196f75a125a55b5f69c86956f5da321a55bdb68886956f79a021a55bdd68476957c7e7799a559fd684969572dd8664c86 else 0x5dff66098596ffda726165fdf69498597feda226165bff2a6885977fca9a2165dffa6688596ffda7a2165bff69a88597f7ca5a2165dff2a1975977fe8865d65bff2a1975977fc9865d65bff6a0975977fc9825d65dff2a5875977fe9961d65bffaa9865977fe9961965dff661865977fd9761965fdf295865977fe9921965dff66086596ffda721965dff65c86597efca95d965fbf26176597efe885d965dffa65765977fd985d965dff26176597efd865d965fbf21976597efca899965fbfa2266596ffca899965dff662665977fc9899965dff65e66597efd8699965fbf5da66597f7ca661565fdf61985597f7c8661565fdf5d985597f7e6661565bff2a1755977fc985d565dffaa9981977fda766065dff29d98197bfda6a2065dff66288196ffda6a2065dffa21971977fd9861c65bff69887196ffeaa61865dff661861977fd9761865bff2a1761977fd985d865fdf25d86956ffeaa61a55dff2a586957dfe7761a55bffaa886957dfda721a55fdf69486957fdda321a55ffb68886957ff9a021a55bff2a1769577fc985da55bff6a076957efda899a55dff2a666956ffda899a55bff2a2669577fc9899a55fdf61975957f7d8759655ebfaa98621bafda561886ebf2958621bafd8665486ebf618865d7afd8621875f5faa9751d7d7da65d475f5f299751d7d7d865d475f5f219751d7d7e665d475ebf61886597e7eaa59465f9f6a165197e7ca859465f9fa2165197e7da759465f9f29d65197e7d8759465f9f21d65197e7d8659465f9f5d965197afd8621a55f3f5d87695777d9525586bbfaa98621aefda526266ebfa219599bafe8825666bbf69c9599aefda521a66cffa219599aefda625666dbf658965d76fca999975dbfa66665d76fc9899975ebfa22665d7afe8899875cff660985973fe99a2165cffa21975975fd9725d65cff261865976fe995d965ebfa2176597e7ca55d965dbf66266597afe8899965bbf69e665976fd9799965f9f99985596efca65d565cffa2197197afe8899865dbf65e66196f7eaa59465edfa2165197d7ca99de55bdf69c96957d7e7725a55f5f9dd86956f7da721a55f5f9dc86957e7d8621a55bdfaa976956f7da85da55f5f61d76957d7d761da55f9f2a666957e7ca899a55f9f26266957e7da799a55f9f29e66957e7c9799a55f9f61e66957e7c8799a55edfa2266956f7da799a55f5f9de66957e7c9699a55f9f21a66957e7d7699a55f9f1da669575fe7725a55dbf2a6669576fc9899a55ebfa2266957cfe7799a55f9f69666956f7eaa5d655f5f9dd75957e7e665d655edfa2165956f7da759655f5f9dd65957e7e6659655dbf69a9961a7fda5a6586df768e9961afdda3a6586ddfaa99521b77da765486ddf29d9521b77d86654869ffaa99521af7eaa65486d7f65d9521b7dd8664c86df76959321) else (if i < 3 then 0x97bfd98a2165eff26288597bfe8865d65dffa64975977fd9825d65effa2097597bfc9861965effa2186597bfe8821965fbf61886597efe995d965fbf66176597efda55d965effa2176597f7ca55d965fbfa6666597efd9899965fbf26266597efca799965fbf65e66597efc9799965fbf61e66597bfe8899965fdf25d85597efd7661565fbf99985597bfe885d565fbf5d975597efe665d565eff69e88197bfca7a2065bff69e881977fca865c65bffaa987197bfe8861c65effa2186196ffeaa5d865bff6a176197bfe885d865f7f61d76197efe8899865fbf61e66197efc8799865fdfaa965197f7da859465fdf2a165197f7e8859465fdf69d65197f7ca759465fdf61d65197f7c8759465fdf6a096957f7da725a55fdfaa986957f7ca961a55fdf69d86957f7ca761a55fdf25986957f7da721a55fdf25c86957f7d8621a55fdfaa976957f7ca95da55fdf6a176957f7ca85da55fdf26176957f7d875da55fdf25976957f7d865da55fdf21976957f7c981da55fdf61876957f7ca999a55fdf2a266957f7c9899a55fdfa2266957f7ca799a55fdf25e66957f7d8799a55fdf21e66957f7d8699a55fdf5da66957dfca69de55dff9dc96957f7da561a55bff69c86957dfe7721a55fbf61886956ffeaa5da55dff2a576956ffda85da55f7f61d76957f7da55da55dff26076957dfd761da55fbf2a266957efda799a55fbf29e66957efd8799a55fbf21e66957efe7799a55effa2266956ffda799a55f7f9de66957efd8699a55fbf21a66957efd7699a55fbf1da66957f7ca65d655fdf21975957f7d765d655fdf99975957f7ca859655fdfa2165957f7ca759655fdf21d65957f7e7759655fdf61965957f7c8659655fdf5d965957f7c7659655fdf999659577fda6a6586dff6969961b7fca5a6586fbf69a9961affda5a6586ff768e9961affeaa65586dffa659561b7fd9765586dffa649561affda725586fdf6549561affeaa61886dff6199521bf7eaa65486fdf69d9521bf7ca765486bffaa99521b7fd9765486bff6949899bbfda5a2266bff69a8899befc9861a66bffaa98699b7fe8865666bff6a09599b7fc9825666bff69c9599affca865975bff6a0965d77fd9825975dff658965d6ffeaa61975dff6a5865d77fca961975dffa65865d6ffeaa21975dff6a4865d77fe9921975fdf694865d7fdda321975ffe680865d7efda899975fbf2a2665d77fca999975dffa66665d6ffda899975bff2a2665d77fc9899975effa22665d7efd8699975fbf21a665d77feaa65875dff6a1961d77fca865875bffaa9861d77fda961875dff659861d6ffeaa21875dff6a4861d77fd9621875fdf694861d7fdda321875ffe680861d7efda899875bff6a2661d6ffca899875dff662661d77fd9699875dff6a299596ffda8a6565bffaa8985977fe992616 else 0x86fff2969961bffeaa65586fffa659561bffda765586fff29d9561bffd9765586fffa649561bffd9725586fff25c9561bffeaa61886fff6958621bffca561886fffaa99521bffda765486fff29d9521bffda526266fff2a68899bffeaa61a66fffa218699bffda561a66fff2958699bffe8825666fff6a0965d7ffc9825975fffaa9865d7ffda961975fff2a5865d7ffe9961975fff659865d7ffc9661975fff695865d7ffda921975fffa64865d7ffd9621975fff618865d7ffda521975fff2a6665d7ffe9999975fff2a2665d7ffd9899975fff262665d7ffe8899975fff65a665d7ffd8699975fffaa9861d7ffd8621875fff2a2661d7ffe8899875fff61a661d7ffda726165fff69898597ffca9a2165fffa6688597ffd98a2165fff29e88597ffca6a2165fffa2197597ffc9825d65fffa2097597ffda961d65fff2a587597ffe9961d65fff69987597ffca661d65fff69587597ffeaa61965fff2a586597ffe9961965fff26186597ffe8861965fff69d86597ffca761965fff65d86597ffc9761965fff69586597ffe9921965fff66086597ffd9721965fff25c86597ffd8721965fff2a576597ffe995d965fff66176597ffc985d965fffa2176597ffd865d965fff69576597ffe9999965fff66266597ffc9899965fffa2266597ffd9799965fff25e66597ffd8799965fff61985597ffc8661565fff5d985597ffe6661565fffa2175597ffd875d565fff61975597ffc865d565fff5d975597ffe665d565fff29e88197ffeaa61c65fffa2187197ffda661c65fffaa986197ffe8861865fff69d86197ffca761865fff61d86197ffc8761865fffaa976197ffda85d865fff2a176197ffe885d865fff61d76197ffeaa61a55fff69d86957ffca761a55fff9dd86957ffda721a55fff9dc86957ffd8621a55fffaa976957ffda85da55fff2a176957ffd875da55fff61976957ffc865da55fff61876957ffca899a55fffa2266957ffca799a55fff61e66957ffc8799a55fff9de66957ffd8699a55fff5da66957ffd8761965dff65c9561b7fc9725586fbfaa98621befda561886fbf2958621b7fca765486fbf6949899befc9825666fbf25c9599bbfca9a2266eff69a8899bbfca5a2266fbf29a8899befeaa61a66fbf6958699befca561a66effa218699bbfe8825666dff25c9599befd8625666dff69a995d6ffda6a6575bffaa8965d77fe9925975dff260965d6ffca961975bff2a4865d7efd8621975fbf6a6665d7efca999975fbfa66665d7efd9899975fbf262665d7efda599975bff2a6665d7efd9699975fbf25a665d7efd8621875fbf2a2661d7bfe8899875fbf61a661d7efc8699875dff69e99596ffda7a6565dff29d98597bfda9a2165eff2a688597bfe99a2165eff69e88597bfca7a2165eff69a88597bfca6a2165eff696885)) else (if i < 6 then (if i < 5 then 0x65e8cbc597732eb65d0cb9597132df65b8cb6596b32d365a0cb3596532c76588cb0595f32bb6570cad595932af6558caa595332a36540ca7594d32976528ca45947328b6510ca15941327f64f8c9e593b327364e0c9b5935326764c8c98592f325b64b0c955929324f6498c92592332436480c8f591d32376468c8c5917322b6450c895911321f6438c86590b32136420c8358f331bf6348c6258ad31436248c3d586730a360e8c1b582530175fe0bf457d72f875ea0bcb578f2eef5dc0bac57412e635c80b8756fd2dd35b50b6156a72d2759f0b30564d2c735878b0555fd2bdf57a8af255d12b6b5688ac755732adb55a0ab155532a8754d0a90551129ff53b0a6d54c9296f5298a4a548d28f751a8a2a5441285b5068a0353f127bb4f189db53a727234e009b2534f26774cb098d530325e34b6896252af253349f09315249246f488890e520923ef47708e451b9234746308b9515d228b44b888c5111220f43d086f50c9216b42b084b508520df41808255037204740387fd4fe91faf3f507df4fad1f2b3e007b74f5d1e933cc878f4f091e033b9876a4ecd1d6b3a907484e7d1cd3395871f4e2d1c2f38486ff4de71ba336f86db4dad1b5736a86d44da71b4b36906d14da11b3f36786ce4d9b1b3336606cb4d951b2736486c84d8f1b1b36306c54d891b0f36186c24d831b0336006bf4d7d1af735e86bc4d771aeb35d06b94d711adf35b86b64d6b1ad335a06b34d651ac735886b04d5f1abb35706ad4d591aaf35586aa4d531aa335406a74d4d1a9735286a44d471a8b35106a14d411a7f34f869e4d3b1a7334e069b4d351a6734c86984d2f1a5b34b06954d291a4f34986924d231a43348068f4d1d1a3734686864cfb19df33906684cbd195332586404c6f18b7312861c4c27182730085f84bdf179b2f005d64b9917132de05b24b5316832cd058d4b0715e72b905674abf155f2a685424a6d14b329105184a1d140b27d84f349d5138726d04d1498d12f725984a9493f125b247048448fb11d3235846248b5114f2258443487110b7212841d482b103720203fb47e50fab1ef03d647990f131dc83af474b0e731ca038a47030de71b8836846c30d631a7034346750cc3193031b46230c1f17f82f545d70b8716c82d245930afb15b82ac45430a5f147028544f909d7135826344b309471250241447308c7115022244330847104020043ef07bf0f301de43a9072b0e101b9435d06930cd8191431105ff0bb016c42c505630a88149428304e70988130425f04bb097012d425904af095812a425304a30940127424d04970900117421f042308180fc41eb03bf07480e241b9035706780c9418302e705980ac414b027704a808d410d01fb03c007140d3018b02d00534095010b01e00334055008700c800f400f00030000fff69a9961bffda5a65 else 0xe0339f14a3938f8780ca7c528e4e3e2e1319f938f8b8781143272605e4e3e2e1e028a09817938f87838a70c0527e126e4e3e2e0a59b938f8b87809e70c26e2e0e4e3e127a01793878f8b80a2727664528e4e2e1e0e3a49b938f8b87803270d0607e4e3e2e1e085a422178f8b87801f903690d45e4e3e2e1e00ca0a09f938f8b878316826282745e4e3e2e1e00cab198ca0cf938b8783169c6622832e4e3e1e0c5a71980a0c7938f8b8716945a6e4e3e2e1e00ca2981d17938f87838a82826e4e3e2e1e0450ca584d49c9b938f8b831690d2745e4e3e2e1e00ca4a09b938f891783849e905e4e3e2e1e0279f938f8b87821432726e4e2e3e1e00c9c17938f8b8780a270726e4e3e1e2e085a0000000000000000000000063e4e2e1e09432221f938f8b878280807e4e3e2e1e09f938b8780604e6e4e2e1e01897938b8780204e688e4e3e2e1119b8b93878c46508e4e3e2e1119b938f8b8420466e3e2e11911944f938b84204661208e4e3e1119b938f885c465872e25e4e3e1e09ca01f938f8b8782728e4e2e1e013981cdf938f8b82628e4e3e2e1119a1a17938f8b878270746e4e3e2e1e045a11917938f8b8782786e4e2e1e00f9a3e1a17938b8782786e4e3e2e1899a1b938f8b862660c60c5e4e3e2e19f1423938f878260c0807e4e3e2e1e0a21f8f8b8780426a4908785e3e2e1e0a2401e178f8b878272785e4e3e2e098a09f17938f8b878286328c533e4e2e1e0a188a314cb938f878286028c531e4e3e2e1a184d7149c9b938f8b82966c5e4e3e2e1e09c1e17938f8b826035db6bb0d755ae935cf6b98d725ae335c36b80d6f5add35b76b68d6c5ad735ab6b50d695ad1359f6b38d665acb35936b20d635ac535876b08d605abf357b6af0d5d5ab9356f6ad8d5a5ab335636ac0d575aad35576aa8d545aa7354b6a90d515aa1353f6a78d4e5a9b35336a60d4b5a9535276a48d485a8f351b6a30d455a89350f6a18d425a8335036a00d3f5a7d34f769e8d3c5a7734eb69d0d395a7134df69b8d365a6b34d369a0d335a6534c76988d305a5f34bb6970d2d5a5934af6958d2a5a5334a36940d275a4d34976928d245a47348b6910d215a41347f68f8d1e5a3b347368e0d1b5a35346768c8d185a2f345b68b0d155a29344f6898d125a2334436880d0f5a1d34376868d0c5a0d34176828d045a07340b6810d015a0133ff67f8cfe59fb33f367e0cfb59f533e767c8cf859ef33db67b0cf559e933cf6798cf259e333c36780cef59dd33b76768cec59d733ab6750ce959d1339f6738ce659cb33936720ce359c533876708ce059bf337b66f0cdd59b9336f66d8cda59b3336366c0cd759ad335766a8cd459a7334b6690cd159a1333f6678cce599b33336660ccb599533276648cc8598f331b6630cc55989330f6618cc2598333036600cbf597d32f7) else (if i < 7 then 0xe2e1e087a03694201f938f8b87829666508e4e2e1e013a19997938b8780604e86665e4e2e1e00813a196819a2387938f88469666508e2e4e1e311a1999623938f8b84468656608e4e3e2e111a19997938f8b8420468e2e0e4e3e12898a19997938f8b87811e928476665e4e2e1e0e3a41f93878f8b80a270726e4e225e3e1e0a01a1f938f88238780329072625e4e2e1e0e3a19997938f8b8780a28e4e3e2e1e0479834301c1814a11f938b87838ec472625e4e1e3e2e028a4a098961f938b87838e907e4e1e3e2e0289e1e9a94a01f938b87838ea28e4e3e2e1e0879cb897938f87821e7080d0cc6c5e4e3e1e2e0a834331b1793841f8f8b82a06050807c6c5e4e3e2e1e0aca09c37938f8b8780329282706c6e4e3e2e1e00ca98f1b14a0cf938b8782960c6c52831e3e4e2e1a4209c14331b17938f878b82b8685e4e3e2e1e09e1a17938b87838e7688685e4e3e2e1e0a0221b938f8b87821684645e4e2e1e0e39c211b938b87838d168282707e4e3e2e1e04645aaa11917938f8b8782828270c45e4e3e2e1e0c6a8a18ccf1b938b8783169286031c6e4e3e2e1c5a41d1917938f8b87828a74645e4e3e2e1e0a1209d1b938f8b878116986e4e1e2e00f983e3e1a17938b8782868678f8685e4e2e1e0a59e3e1a17938b878286886e4e3e2e1899e1b938b878e266686786e4e3e2e189a19e1b938f8b862670d07060cc5e4e2e0e3e1a830201b17938f87838836a0ce4e3e2e1e04547a31583938f8b84327c560e4e3e2e10c9c37938f8b878032707c5e4e3e2e108e00da4a3158a33938f87828474645e4e2e0e3e1a0239389178f878270d0c06052807c5e4e2e0e3e1b037938f8b878032761c5358c26e4e3e2e0a437938f8b878032706050807a6c5e4e3e2e1e0ac3714a01f938f8b87829c6c5640739e3e2e1e0a71b14a3938b87804e8c6c528e4e3e1e012a31b15841cdf938f8b829c6c528e4e3e2e111a3938f8b87801d22747e4e3e208e0e10ca21c178b938f8384328e4e3e2e1e00c98159a33938f8b8782806852847e4e2e3e1e00ca81a14201f938f8b878032ae4e3e207e1e0850ca0211c9b938f878b803290d080687e4e3e2e1e085a83418201e17938b87838ea084647e4e3e2e1e045a41a1f938f8b8782143694745e3e1e0e4e20da01a991f838f8b87911690847e3e1e0e4e2450da4a11c9b938f8b87811694607e4e3e2e1e045a3938b878f801e666a487e2e0e3e110a19a91a2421e178f8b8782a6687e3e1e0e2109c42919a421e17838f8b86a90a4688785e3e2e1e066a99a42901e178b87838e966a4900785e1e3e0e2a4a09b8f879382178a82726e4e3e2e1e085a3938f8a17809e60c28272605e4e2e1e0e3ab938f8b8781143270c2628e4e3e2e1e027a4a3938f8b87809e728e4e3e2e1e0279f14a3938f8b87809e8c528e4e2e1 else (if i < 8 then 0x4e1e3e2e028c5a0a29c1d1917938f8b8782a4846e4e3e2e1e04527a51d9b17938f8b8780329260528e4e3e2e1e00ca41c9817938f878b80a2987a68545e4e3e2e1e00ca99a17938b8f8780a0329076626052d0ce4e2e3e1e0af938f8b8780a03278c62e4e3e1e0289ca01c983017938f8b8782a46c5e4e2e0e3e128a21d1e991916143023938f8b8782d07462d05e4e3e1e2e028ab189b90178f8b8780a2945e4e2e3e1e0289d1c37938f878b803280d4726450c08e4e3e1e2e0ae9b938f8b8780a03280d08472645e4e3e1e2e00cae301c14309b93878f8b82a470c8545e4e3e2e1e0a6a91f14201917838f8b8792a4c0887470685450d0ce0e3e2e1e4b8a3189a221c3317938f8b8782ca6460c87450885e4e2e1e0e3b2991917938b87838e80d26850c08e4e1e3e2e0ab8d16208460ce4e3e2e1e087a51833938b8f87821e80d0cc5282d074626e4e3e2e1e0b4203433938f878b821e926e4e1e345e2e09cb53099161793878f8b82a2d4c86264585e4e1e3e2e0ac31201d14369a1787938f838ac28850d0c06e4e1e2e0e3a83214341f8517938f838922b2d4c86852645e4e1e2e0e3acb5321b9386178f8b801ea0748e08d170281224c607e40ce1e3e2e028a4a2991a17938b8f87821eaa68545e4e3e2e1e04887a9209a17938f878b821e963c0a04591189a179385178f8b801ea05e4e3e2e0e10c47a19830201c17938b87838ea08e4e2e3e1e0479ca19816301f938f878b82a286605e4e2e3e1e047a61a17938f8b8780a03290d8785e4e3e2e1e0480ca8a19a1f938f8b8782169668785e2e0e4e3e1a21f938f8b8782159a847841e991b91178f8b8780a2a26e4e3e2e1e0c528a218361c982217938f8b8782b08a60647e2e0e3e1e445a89b1783938f8b851e826c5e4e3e2e1e087a299181d17938b83878e9080d07462645e4e2e1e0e3ac3717938f8b8780a21e928060d0745e4e1e3e0e2a89a8d16388288727c6260ce4e3e2e1e0c5b4311b938b8781178e8a360858c3318a09b938f8b8783149eb08e4e3e2e1e0c527a0231b938f8b8781149e91308c6e4e2e1e0c527a448231b938f8783149e91108c6e4e3e2e1c527a4321e189b938f8b878314a2b0d45e4e3e1e0e248a120309c9b87938f8b8316a452789211917938f8b87809e90c48c626e4e3e2e1e0c5272c301f1b93878f8b8314a2aa60745e4e3e2e1e048a4318f0230c64c0a09000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000393878f8b812260605e4e3e2e1e00ca18f938b8782563e4e2e1e09496221f938f8b8780329888766e4e3e2e1e00ca6221c33938f8b87819a90c660807e4e2e1e0e3a43416221f938f8b878032a0588e4e3 else 0x268564a3c0940000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000666547e4e3e2e1e048a5211d9997938f8b87829e4e2e1e0e3659923938b87838e6080726250ce4e2e1e065e3ad8f938b8782526a5e4e2e1e0e39d211e99983297938b8f8782b0d0c2625e4e2e1e0e3a431211d9b938f8b878296a080766260d25e4e2e1e0e3af8e12625e4e3e2e1e087a2199a143094201f938b87838ec086625e4e3e2e1e087a6238f938b87821e788e4e3e2e1e08766a0209a97938f8b87821e966a50d260c250807e4e3e2e1e0b499978b938f83861e84760288f189b1497938f8b87811ca2b28a3070f189b1494a3938f8b87821eb0c86662508e4e3e2e0e187ac9b938b8f87821e76607e4e1e3e2e0a5a0a19b938f8b87821e80de4e3e2e1e0280ca034181433938f878b82928078685e3e2e0e4e10caa17938f878b809c3280d8828872706050ce3e4e2e1e0b434331b17938b87838e9c6c508074645e4e2e1e0e3ac34201e191a151433938b87838ed060528e3e4e2e1e027a43430a38f938b87809e908864685450d070ce4e3e2e1e0b51830a38f938b87809e928e4e2e1e03398a38f938b84c6607e0892382248c6c5e4e3e1e2e027a43522191a1514301f938f8b8782d480605e3e4e2e1e027a4341c33938f878b80a290d0c8646854507e4e3e2e1e048b5821e263a0881e82286e4e3e2e1e0859e1b9386178b838e786e4e3e2e1e0859ca09f1b938f8b87831694645e4e2e1e0e39c211b93878b838d1682806e4e3e2e1e027c5a51b938f8b8781149e84645e4e3e2e1e027a0a3938f8b87809f1a828c6e4e2e1e033c5a0a31b938f8b84c716845e0078c1b938f8b87809f168c6e))))
def lay61r11 : Packing := (782,3,5,63,0,15,1,word61r11)
def keys61k12 (i : Nat) : Nat := (if i < 2 then (if i < 1 then 0xbc7e68380000062e0207363f5069063065e630d4f25c64f0e1aad89a7490749a00fc3e2b328019dba5251056a1bc00002ec4749fd02b58b7f1a152d9844c9135b14ba1e001b0b06860c9d0147302e2ff870d8411f250610de24a75f6c8df2a8bd84f509b79fd0000113ce27ba2cf657d08ed96fae05a9243c09a205b8195c912c94a624ba4d432c11de538ef9b09129e6ea311a6d11bc0570000f09fa83c612e10306662b8ce904e308000002240de2a72fcd0b300003ed4a1f22175000072f1d12d82bee2ef129d859ca1f34c7de27721260000ae4addd500005ac4c26dc5e1c9cde87c614a15eba2d3e9cca0ee902f95f98032dd4e4a11a0f830af50ab12ce39baa13e42dd4261602e8a3a9282b5616a2101b9c9a7102d819191a0422aad15e0e3b257b268f181f90201e5aa04edf570b2d50da93bf5f1206e6179c6075029d05de95f50a0426cc001d098d0a1b2d220421115611aa03ef0b7f07215e0b60f5901c309b11462de401340159ea08570e18a42e14a20384010e292b328f49a069a24f2fbd258656f514012d086db5097b25a2136b5f5f4da023870cbc820210942ba09d0d962787d760300000000000000000000cd73089cd197f278aa9db23e811c0000e220000031eee19d2e202155c0d17141b171a8c026820000641fe0260000000044c0a0cc510b0000000000005aab81caa081000001feb01f080300003478b42122dafa3fc9da3942c1c4ca30e205016bea9570e9666900917ea6e6e331b5612afd55e9732254a1c9318e5051d2dc2e40830c3e4b117aceb109f7a0b84210e4bd80c02800050413070c0204020a18040d052f02040500081e040d00003576002c001002080700002400900b000006143d00000627022b07220a0100020e1d2c420206000500730018b40701000200050821020e0805230e1004161a43150009000b111a002b0728061b000700116825120d260600111cb9001f1200cf0b162e730a0400001901000404020803010011022b240c2a000d0a00062b040a1e49461d1900000000500b7f011500000a180366040d0000050000000242004100040901021e00003b4d0916060003000000040000040c000812183d23010000000200126707286216000b58010c02070000197e03000d01022e000200080905110201000000a61c1e154e0028000603650b033f2a0f020200000003000037000b290e1619431d0000093c000016002b004c00250006050d00650300350019000d0003003f8a081b00000b07010b000f0000500003d1002a030000020e0216000008000403000001203d02000a05024a059a2700140f1a0656000013000e015a4c0024040222151a1302000004191311550063620400001303000a7000070e1d010002002e0c0000010f42090b25053d3c004f08191d060159000300000b00e3 else 0x9e29417b2a96e01a3966309223041294885a30d3000070dc05b00000f2870000000000000000d2f46604000072320000123a0000c04b0000f1e100007034384e700ad2b0e9df3e17f938e1009a85810200000000000060d829ed71c5e24551834235100eb30bd05230ddfa09cef60477000059f001657e1f113a0000d112e20e205e4402e20b322e853d0000000050b9c1c332c7fa7681acaec6b4196ea788e3c28f000051f03c9af2c010ff00000000c2ee0000fe4d1e41000002bcf829ddf9a98f82eb458fe6810000f170000012d77b04ca360000000000000000216f6a932eae92040177b2dba6e6f68951d831be5b010000867b304895cb014ceae80000118c00002255621c2190f00b806dca7a22cdf131ca8985da10caa6704036918f121ef631d12352f2c1fab2007088e1dc7111000000001266853210d2c5fe613b614e2225922b30e520eb9aa7e1ced2c4c1dd407a45126592a1c2507cb5ce0188d01cf08b041dba8aa26450cf6e3fd4d87290a4e474f41117c0ac701b52bbc5b7c9c739600891495c92b2dd25f07b41992ed5515d5a989259f06cc16acea9b2310020a163d8ec0237b24652b7b0a39e4cc0fe469e42231307e1d43e2e5ab9ca1041292289f2c918c5c168d53a205fa306b625e271b1da408758faca3d7658f208409578ee283f3c9131464d742af6d039f1f7e2d852c28e1ef0fae12c716e3673a496965586f6a20d0274a18d2c2060de115e4e169d7dda23415852830cc090ec4249917f2a7f70ba807f059ec5fb8079cd3256ee681d728dc1e67c21002a655651c099de21345805e5b661336847faa435d391ab0025d2027050f058d99135e5c2fd90daa666c128f19441a26a2cf1c7354e025b3ece5ecd24058301d154316275495070e29c914db10eb2e3c00dc1cd46680de6688f36a7f27ad07d657c808ea6f8bcbe74756b05225d065d724732a161b4d80f726a90ed501dd485a0215a94e07475dcd02871d632a07041b0ceed61828b29e231b340f6827fd2acd9fff256523f0027bd7561b602c622cbda8776c6ecf4a1133107f1de02c548ea610a31ecf6aae80621eaf9f390551857e641345476ea9c9201430151d4e551986180e149a6019119ba0be0cd2a9c02a62ca6a1f80c1051734d4b8064c0a282b990c7fa0c4305324cb2afc649004dd817104c42a222a90139685ca093f23d01d268f0f9c11a3222348054982395d76296342462b1221d526b101199a56085dafc6189890021d76298000004d30000a000d161912460659059ee9ea2e04a7760f435a50000d19ab30d0000d035321721edb0d65227019f5e25119cf0d710f10000016640a421cbd566aa0ea11e0000c53c10f201f95178b0b00000b444f9d1368796a934e1213d81a522360000c1d9862070e41a99a9dd0000) else (if i < 3 then 0x12abab0ba219e089559552bd62111076a941b0f0c07791f591a365f840948230d22811204ea230a76aede00722b635d272d161a7e501b08c1281401031b1593642b46493f13f1679e0189164618278dd22a352aec2d481e489dcd2e642e9b23912a8417c812fe265a0081a8c366ec555c233307379bb42a5425fb262b28670c5819366e01196a2f9aaf859b49c7f6a6af12be916b22dc045806021e960bca9e3508336a6166d1a6fe8a85d7ea09c61dbfa083a226224c41741d17aba18d9fe8291457147f602e6400000f64b60e096b19819018585d9b038ea3eece4527dd28e4d1e3003b8d20000fd4a00000000b18bf1b791a80053000011fc8eca41f110df0000204ff680c1fd014f304a209960b1f2e8da7292df80e7b5a1f293704742150000991b34e358d1621bbdd4029b00004d14c269467100000000f15b4242803b61ad00000000d12222f60000c87ff03c6d50b4b4224e000000008ab841440000541866c10d8f96724152e1cc5a97f5e4baca119b2d6c21a4f969c2e2ce27106bd30a0000000078529e21c12791f49ecb3e330000c13711bb359d0000f118f1fb20be6148f9ea2071b65f0000242eb0c1915630db811600000000c2ad60e6ea92b0aa0000000000000000d534000000fdc03f0000a0e8e1bf60c384dff1d3269fa28499eed4e984dc0000a1df0000b1384106528595b9b517f8ffc4cf896d11e7a1530067749de0f5e9d492edde9daa7dc5e3d2f8203730f900000000d4b10000000020a93061b07ea16c8192e2ea6c62426faa5c32bfc2b5596c829982f5d21f301e2957c0127844f09d000090bf0000a58b06e4323c3e9b623b52d600f300009875f303f2a770c83a6c66ef208d1498f0b422aa9160d103a15c0000027310a556cac105859ba9140000000000002082922f0000f24f0000f4d170b50000000000005ecca10854acc2e42e9530ae000044b574fd71afb2069142b47231e819b6000052a4cc1d325e82185d1dc1b209336078e10f51d549f8843cd947fa86e1ebc22c4251c267f11f6491220a150c90bba84d51cfb84caa03d4e669e92244a040e2ec0845285515df92723940906272fec0d082b8967a00009297b1c8cdfa00000009908ada8d051400000000422620d5f16901300000f4550000b66f00001a8e01c1a850c91598e8620190310000000060e1c19e89442b0000009ea189f1821358d661250000b8c2000012410253d002310c10669a7900000e2600000000b16d90a8824d321a00000000000072c3d1c640192046856b0000e03389f6c9fc55d5d0c6a121d55f517dc492428a503d000062cc69d90000000039f238e703000000b8567222ca903410606ac0ef20b6b09ed8d400002db67086c2fa7279c186a0fb062f26f799c5ce9ff184fda582f3955a1090429a70ad3270322161bd00000000 else 0x15d412ca0e2361e3465660840000a4b2717ec03a68dea1f6596791e2b0053807b2915404d0d90000000092038174021422e748beb499c90400005557554a6a8062480000747b3023f1a90000c5509260b5fa2413f6887af7c935f049d9e0ca8800006216dce5b209615030bd493d000081579ec5ea6e39eca004d11094d2015fd11d2176ee8311d09aa6b8a6f276f0752a130000d57a165e71b86816710172f085732911f8e200000000c93910c4b9e854a6450712d5fab189e1001752f7aa01227cf5ba8308f6d45e9c8024a0960890e022c2926961f8d8c8f2c26ee2c8e443b1670000664a31ef047d7187f27ea00c608f00004044a0a65016145f98fc210469650000ea8421ff19f500000000d00f000022880000b1ae96540000cac50000822959e790eae6abd93e806f113279cac8c83006e1ba00004683000000008a9f0000a47640f7c8c3e212920f3c90e275428c551500008b0c229fc0c2726361725295b02ca15a3159420c5063a25222e53043b05c))
def cut61k11p0 (i : Nat) : Nat := 0x13
def face61k11p41 (i : Nat) : Nat := 0x1e7
def cut61k11p42 (i : Nat) : Nat := 0x26130984c2600008341a0b0582c260e
def face61k11p208 (i : Nat) : Nat := 0x3e9e0188031006203ce079cf9803c207847c40c1810e219444b441d11ee707440e886111ec20304079c03112d13d4407200e412a831940720c6518b0039007206b41e9107441ba41d110e200c4018887100623cd20720c6503a20dd2438803112a807440e880f38062074407200e400620784072095403a2
def face61k11p272 (i : Nat) : Nat := 0x124f33200e88f7381e700c40e881e103a2
def cut61k11p281 (i : Nat) : Nat := 0x130984c2613098341a0d068341a190582c160b0582c160b0c040260e
def face61k11p463 (i : Nat) : Nat := 0x14c229842d094802900520097092e129003f8497092e12880168497085a10b4216849708fe11f8216842d092e1290051007e0948035c62a38a40148029003a80a40144033dc2304871006221c401880311c4129006a0cc5808c121c4018800013b02900694097092e128805100a2012e125c24b84a2012e1
def face61k11p527 (i : Nat) : Nat := 0x7847e081e11e0838820f081e11c4107845100a2003c230607820e209c8e34006800cd01f823ee20e881d1156207440e881d1156238825500d0003a2078466801d10ca2030452000001480194460c0a40148019443a8046090e200c445b88b7116e22dc45b88b7116e22dc1684a2005a10b423f042d085a1
def face61k11p591 (i : Nat) : Nat := 0x52000000a8e151c2a38a2008c111820188f041e0838824820904120831607820e208000316000000000000000000000000000151c0e880310062074401881d100000744018854710c3154666408619440288051001e11c41
def cut61k11p639 (i : Nat) : Nat := 0x733720934a24d269349a4d25704822da090482371b915823ae08eb75d02088040201011e402010080403410080402023c804020100804034100804020100806130984c2614799c5f
def cut61k11p703 (i : Nat) : Nat := 0x1209048248f478804012285434850a8672a150ab142d350a844824698904824120e0814840090484082371b8f96e501b8e66e37209048c5060904a4371f2dc6e3c1b8e66e371f2dc
def cut61k11p767 (i : Nat) : Nat := 0x47a3d485452150a85447900808f2a100c2
def word61r12 (i : Nat) : Nat := (if i < 1 then 0xa6c3931e0c51684f931e2c381345a03c64c9f263c587045a84070c17262c3831d218288c98f161c01e9c583261c62260c942880e33263c58705623263c5870079c464c58701398464c78b09199325c98f161c01e84c943a8c9871e2c14a64b931e2c1843d01f261c78b0259c305c583263c21e80f930e3c58044e223458f931e2c38294c94407c98b0e0c74a8c98f161c01e71018625c98f160c21ea101c68c8d171e4c587056182c68b931e2c3803d41e345c793161c14080c17263c5870501e364c78b0e08b4080e18645c98f161c15068a33262c787050162e4c78b0e0114088d17263c587050304268a37263c38b054153068b930e3c58298c1e2e4c78b0e0a04071993163c38280c1c2e4c78b0e0a0447c98f161c1168109830d0f902e3c5870561f263c5870459f261c78b007982e4c78b0e04d3a64e17263c5870509a2e4c5870639d30551153e4c78b0e0a9345c3931e0c53a78b931e2c381350993c5c98f161c1426c98f161c11670b931e2c3803cf1b263c5870459c6260b8f262c38284c1c605c98f161c1480000203e4c78b0e09d1882793161c13a01047263c5867c98f161c12860b931e2c38271e182e4c58704e1b263c5844cc908070b8f161c14268b931e2c38278b931e2c3826c99e3f3199887c215ff6f39749b895b36d2d64aafbd676a95513a6752268974149e0cd826532e4948c8de3d71918a643e615b06180e3f5df32f5478ebb45cfce4070136d9ae2d2c67e32a58e4c426092f5171eb5158d2b7154aa6050da79133094547ca2ed0fa83f3f99ed4eee7393769aa0cd462c2f716c0aba52627b12fc90244a1ff0f1c71234b18a0b7454c268111887442e2110ed068c2d8143086035414a0670180003ffd32c37ff65586ffe4ab0dffd8621bffb2a437ff26266fff444cdffd8699bff92b337ffa6575ffecb2ebffc965d7ffb0cbafff21975fff332ebffd861d7ff90c3afff99875fff4cacbffd98597ff930b2fffa2165ffecbacbffc97597ffb0eb2fff61965ffe432cbffd76597ffcccb2fff61565ffebaacbffe88197ffb0e32fff21c65ffec30cbffd76197ffcef2afff61a55ffe434abffd76957ff8ed2afff99a55bff4cb0d7fe9921bdfb0c435ff65486fbeca90dfdd9321bff320437bf66266f7e4c4cdefd9599bdf92b335ff66266bfe4c4cdbfe8899bdfb0d337bf21a66bfecaccd7fe995d6ff92cbafbf99975bfecb0ebefe661d6ffd32b2dff66165bfe4c2cbbfe88596ffb2eb2fbf5d965f7f332cbf7d85596ffb3032effa2065bfecb8cbefe66197efaca32fdf25e55fbe4b4abf7d86957ef90d2afdf5da55fbe3b4abf7e66957bfcef2adff25a55f7f334abf7d75957efacb2aebf61886ebeba8ebe7d65196efb2a435f764c86bfcc810dafe8899adfb2c3adf764c75bfcc80eb7bd94197afcef2af9f99a55 else 0x4c94407c98b0e0c74a64b93161c18e7c98b0e0c69664c94464c5870630f4a64a23263c587007a532551930e3c5803d2223268a943a88f931e2c382d8c9a2a511930e2c18c3d7930e3c5812879c305c98f161c03465237263c58700c9e3451a9c663c98b0e0a86880e32345c98b0e0c758d0e314468a9f1e4c587058346078d153e3c98b0e0ae364c5870638b3a84f1b263c587045a43a78d931e2c3822d21c2e4c78b0e019426c98b1e1c03270e982c55033263c5870561e3260a3044551931e2c382d4d931e2c38064e1628cc98f161c09a9101c68c4d171e2c3930562232618143c5c987163c160c8d15464c78b0e00f50d18182874d17261c78b05919345c9871e2c01e9101e3260b931e2c3806561c3054d931e2c380654213288f931e2c3822d435347c18f161c9169511f263c5870268b4a60f93161c18e2d035307c3931e0c5169c98f161c09a2ce203c64d93161c18e2d41e326509f263c587045ac3)
def lay61r12 : Packing := (102,2,5,63,0,13,1,word61r12)
def keys61k13 (i : Nat) : Nat := 0x68ec0004130005b4301400000000030b600049f000000064a70c68ded53048a4e298b38b34099fc094120a462819d8c8bf258216496485a005d61bcca41ac2832880d6299a34c115135a1fc163899968ac811250ba0ca297161f2e8f0f28e24e0007671448b1f21fb15888190956db4c7c9201bf07e07556b233e0ab15481c20c40f7f2d50760049a8ab0c4c2ad620f065550a3ea2e70180019a2e5ed24e0a6511f2811978059b5d1c00004284207047a15e35fccd6630eb5967c75a10001035010213b90c001c8f42f4827629057a510b1c000d2ba4074900004a6315e31800000041080014068dab9e8ab94a513cc5f601e884839b14bd24c88f8346f071acc109411e435f862938d094574a2d54328afc00d724a719bb43991b02f52a0000c39aa100000b850e0000000915c7bc97ee8208e4c7c1f083892c57800421560c04994640000000000a47427ea4bc2340156a0987c16f8700058d859c00341063800b0010403810410c8084480201024f84182000c3a28104280c080063c28a06301000000080020c1110800b010208699
def cut61k12p10 (i : Nat) : Nat := 0x4c1a0b
def word61r13 (i : Nat) : Nat := 0x61648a18239c61481e48e2860a461479238a18281858e48a18271a48e28601671859238a18271e48e28601671a48e28601679238a18251648e28609b61749f439bcae3f1385400ffd86ffc86ffe66ffd75ffc75ffd65ffc65ffe55efe66f7e55
def lay61r13 : Packing := (10,1,5,63,0,9,1,word61r13)
def keys61k14 (i : Nat) : Nat := 0x180ccf62f24000030200000a040000000000007d000000000000000000000000000058c000014500000d100000207001d1001930000000397002e0000000000000243e20000000000000550000028659000000000000000000000000000100
def word61r14 (i : Nat) : Nat := 0x20c4104bff
def lay61r14 : Packing := (1,0,5,63,0,0,1,word61r14)
def lc61k9p0 : Array (Bits × Bits) := #[(0x640c40560407b,0x6609e05600053),(0x7ff400074521b004,0x7ff408014530b9b3),(0x34784183a2188,0x1578c0a08204d),(0x4011805a43e08,0x4000005ac201f),(0x862069c7f000,0x8a0148cff485),(0x887c08e07c00f,0x897400a0f440c),(0x7ff0f800f007fff0,0x7ff08801f013dfa0),(0x7fff0000fff80000,0x7ff62012b5300932),(0x7fffffff00000000,0xb75fe02000040)]
def lc61k9p0ok : LocalSamples 511 := ⟨fun j => lc61k9p0[j]?.getD (0,0),chart_pairs (by decide +kernel) (by decide +kernel)⟩
def lc61k10p0 : Array (Bits × Bits) := #[(0x348f0ad00b,0x34cb08d019),(0x7fffff0402ae4164,0x7fffff0002ae6130),(0x59bb001aa6,0x51bb000a0e),(0x20030ddc17,0x200209d817),(0x232316726,0x212a12726),(0x433c4187c7,0x43344106c6),(0x7fffff83c07e07f8,0x7fffff0200f625e0),(0x7ffffffc007ff800,0x7fffffac401ed010),(0x7fffffffff800000,0xdded000008)]
def lc61k10p0ok : LocalSamples 511 := ⟨fun j => lc61k10p0[j]?.getD (0,0),chart_pairs (by decide +kernel) (by decide +kernel)⟩
def lc61k10p1 : Array (Bits × Bits) := #[(0x4e8701a5010d1,0x4e85c125002c1),(0x7ff8880178012c2e,0x7ff8800979210e04),(0x3550041a4930,0x255e040a0138),(0xc10616548630,0x810a16508230),(0x1019860670830,0x10a20a70830),(0x207e08787f03f,0x7a2848ef13a),(0x7ffc0600f807ffc0,0x7ff80201e9a57c04),(0x7ffff800fff80000,0x7fffd8015b500285),(0x7fffffff00000000,0x77cf400080189)]
def lc61k10p1ok : LocalSamples 511 := ⟨fun j => lc61k10p1[j]?.getD (0,0),chart_pairs (by decide +kernel) (by decide +kernel)⟩
def lc61k10p2 : Array (Bits × Bits) := #[(0x2207c034100873,0x2305c814150851),(0x30091ab520580c,0x10011ab5a31d08),(0xc23d80483fa1a0,0x42bda00a2c2227),(0x31608d202620,0x11280d212224),(0x8418309c0c830,0x8012208c0cebc),(0x10c7e040e00f03f,0x10cfa200a08e2a6),(0x7e0f8007f000ffc0,0x7e080017e082d588),(0x7ff00007ffff0000,0x7eb1001df5130140),(0x7ffffff800000000,0x1e7eec0020c0043)]
def lc61k10p2ok : LocalSamples 511 := ⟨fun j => lc61k10p2[j]?.getD (0,0),chart_pairs (by decide +kernel) (by decide +kernel)⟩
def lc61k10p3 : Array (Bits × Bits) := #[(0x2590e4006e00f6,0x259066402e80d3),(0x7fc18120e5c41689,0x7fc0802065c49291),(0x611f4001bca02,0x411fd0019c052),(0x62701ae610e,0x22840afc01f),(0x4838060c720c,0x40282409f21c),(0x186fc018307c0f,0x86f8908116c0c),(0x7fe070001fc07ff0,0x7fc040003f403f20),(0x7fff80001fff8000,0x7ff3800253e60001),(0x7fffffffe0000000,0x3f3dd780000040)]
def lc61k10p3ok : LocalSamples 511 := ⟨fun j => lc61k10p3[j]?.getD (0,0),chart_pairs (by decide +kernel) (by decide +kernel)⟩
def lc61k11p0 : Array (Bits × Bits) := #[(0x88103b01ce0cd,0x88102b00ce041),(0x7ff00804995ce342,0x7ff00000895de140),(0x4333e80206474,0x413be80002054),(0xc018a046f847,0x80088006e857),(0x10420c1809f44,0x40081001f54),(0x6063f06071f87,0x406bd02021e96),(0x7ff807c007f81ff8,0x7ff0044007f117a8),(0x7ffff80007ffe000,0x7ffbe80004fdc000),(0x7ffffffff8000000,0xf7bb770000000)]
def lc61k11p0ok : LocalSamples 511 := ⟨fun j => lc61k11p0[j]?.getD (0,0),chart_pairs (by decide +kernel) (by decide +kernel)⟩
def lc61k11p1 : Array (Bits × Bits) := #[(0x75d006400d1011e9,0x75d0024405140189),(0x18081c81006116,0x8000c81202106),(0x606840121e8620,0x406860020e0421),(0x80306023530838,0x106403520038),(0x1004180c0638000,0xa040a38000),(0x6067e030383f03f,0x2067ca1028bd430),(0x78078003fc03ffc0,0x802808bf8a1fa44),(0x7ff80003fffc0000,0x7db8000ebd500084),(0x7ffffffc00000000,0x77f56f10000c0481)]
def lc61k11p1ok : LocalSamples 511 := ⟨fun j => lc61k11p1[j]?.getD (0,0),chart_pairs (by decide +kernel) (by decide +kernel)⟩
def lc61k11p2 : Array (Bits × Bits) := #[(0xd00620044083f3,0xd00224004003a3),(0x10083e1881220c,0x2e18810209),(0x603920027a1c10,0x42396002381490),(0x8030c019844010,0x80104409940411),(0x108410062878020,0x8004222178428),(0x60c7e018307e03f,0x20e7c408236f414),(0x780f8001fc07ffc0,0x808800bf403e848),(0x7ff00001fff80000,0x7db0000d5dc00103),(0x7ffffffe00000000,0x77776f9000201182)]
def lc61k11p2ok : LocalSamples 511 := ⟨fun j => lc61k11p2[j]?.getD (0,0),chart_pairs (by decide +kernel) (by decide +kernel)⟩
def lc61k12p0 : Array (Bits × Bits) := #[(0x46c03406e125,0x46c01404e020),(0x7fff80c04644c262,0x7fff80400444c220),(0x30a44093c28,0x20a44011820),(0x4028011e8b3,0x20001e823),(0x80308614f22,0x200410f22),(0x3033f1818fc3,0x1033e0810dc3),(0x7fffc03c01fe0ffc,0x7fff801401fa07dc),(0x7fffffc001fff000,0x7fffedc0013ee000),(0x7ffffffffe000000,0x7fa9fa000000)]
def lc61k12p0ok : LocalSamples 511 := ⟨fun j => lc61k12p0[j]?.getD (0,0),chart_pairs (by decide +kernel) (by decide +kernel)⟩
def lc61k13p0 : Array (Bits × Bits) := #[(0x3a0c1a86,0x3a040a06),(0x2202e01f,0x2002e00e),(0xc302666,0x8300426),(0x30100707,0x20100607),(0x120c586,0x1004586),(0xc1bf05fb,0x41b905f1),(0x7fffffff01c3f9fc,0x10143f1d8),(0x7ffffffffe03fe00,0x7fffffffb602ba00),(0x7ffffffffffc0000,0x7ffffffedeac0000)]
def lc61k13p0ok : LocalSamples 511 := ⟨fun j => lc61k13p0[j]?.getD (0,0),chart_pairs (by decide +kernel) (by decide +kernel)⟩
def lc61k14p0 : Array (Bits × Bits) := #[(0x1c70d,0xc30c),(0x30451e,0x10450c),(0xc041af,0x40410f),(0x7fffffffff0041cf,0x418f),(0x2496f,0x416f),(0xfb077,0xf1073),(0xc3e78,0x43c70),(0x7ffffffffff03f80,0x7fffffffffb02e80),(0x7fffffffffffc000,0x7fffffffffeb8000)]
def lc61k14p0ok : LocalSamples 511 := ⟨fun j => lc61k14p0[j]?.getD (0,0),chart_pairs (by decide +kernel) (by decide +kernel)⟩
def ls61 : Nat → Nat → Option (LocalSamples 511)
  | 9, i => some lc61k9p0ok
  | 10, i => if i<175 then some lc61k10p0ok else if i<214 then some lc61k10p1ok else if i<253 then some lc61k10p2ok else some lc61k10p3ok
  | 11, i => if i<191 then some lc61k11p0ok else if i<376 then some lc61k11p1ok else some lc61k11p2ok
  | 12, i => some lc61k12p0ok
  | 13, i => some lc61k13p0ok
  | 14, i => some lc61k14p0ok
  | _,_ => none
def samp61 : Array (Bits × Bits) := #[(0x31400c2100201f83,0x11c0042ba0001c92),(0x50794c3100dc107c,0x10b94cbf105c901c),(0x1401021f915e180,0x3400122681125a1),(0x11806631061a01c0,0x1280463b0a1021d0),(0x1e05803e07dc0100,0x161500660fde6108),(0x600607c007e001ff,0x660403404fa36161),(0x7f80007fffe00,0x437b8c415eec208),(0x7fffff8000000,0xa2fc9990008812),(0x7ff8000000000000,0x69400100e0010c23)]
def cols61 : IndexTree ColumnInfo := (.fork 13 (.fork 6 (.fork 3 (.leaf [(1,0,510,0,13),(2,0,509,0,13),(4,0,507,0,13)]) (.leaf [(8,0,503,0,13),(16,0,495,0,13),(32,0,479,0,11)])) (.fork 3 (.leaf [(128,0,383,0,11),(64,0,447,0,10),(256,0,255,0,10)]) (.leaf [(33,0,478,0,10),(34,0,477,0,10),(132,0,379,0,10),(0,32,348,131,9)]))) (.fork 6 (.fork 3 (.leaf [(0,128,331,52,9),(36,0,475,0,9),(40,0,471,0,9)]) (.leaf [(48,0,463,0,9),(65,0,446,0,9),(68,0,443,0,9)])) (.fork 3 (.leaf [(72,0,439,0,9),(129,0,382,0,9),(130,0,381,0,9)]) (.leaf [(136,0,375,0,9),(258,0,253,0,9),(264,0,247,0,9),(272,0,239,0,9)]))))
def lv61 : Nat → Packing
  | 8 => lay61r8
  | 9 => lay61r9
  | 10 => lay61r10
  | 11 => lay61r11
  | 12 => lay61r12
  | 13 => lay61r13
  | 14 => lay61r14
  | _ => emptyPacking
def ix61 : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 22 83 6 11 7 0 keys61k9
  | 10 => lookupWord 337 1145 8 16 10 2 keys61k10
  | 11 => lookupWord 815 2764 9 17 11 2 keys61k11
  | 12 => lookupWord 442 1501 8 16 10 2 keys61k12
  | 13 => lookupWord 62 213 7 13 7 2 keys61k13
  | 14 => lookupWord 6 74 3 10 4 2 keys61k14
  | _ => fun _ => none
def g61 : Forest := ⟨511,14,fun j => samp61[j]?.getD (0,0),cols61,#[[],[16,66,134],[32,65,117],[64,33,117,134]],lv61,ix61,noFactory,noFactorySound 511,ls61⟩
example : (localWires g61 9 0).length=9 := by decide +kernel
example : (localWires g61 10 0).length=9 := by decide +kernel
example : (localWires g61 11 0).length=9 := by decide +kernel
example : (localWires g61 12 0).length=9 := by decide +kernel
example : nodeVerified g61 13 0=true := by decide +kernel
example : nodeVerified g61 14 0=true := by decide +kernel

end PEqualNP.Outside.L_meta_11008

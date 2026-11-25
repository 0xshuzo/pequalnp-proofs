import PEqualNP.Defs

-- The Live/Run/Forest checker derives from PressF10, pequalnp-proofs PR 4332,
-- and its extension in L_meta_3853, licensed under Apache-2.0.
namespace PEqualNP.Outside.L_meta_11008
open PEqualNP.CircuitLowerBounds
set_option maxRecDepth 16384
set_option maxHeartbeats 0
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
def motifEval (t : Nat) (v : Nat → Sig) : Nat → Nat → Sig
  | 0,p => if t.testBit p then one else zero
  | d+1,p =>
    (v d &&& motifEval t v d (p+2^d)) ||| (~~~(v d) &&& motifEval t v d p)
theorem motifBit (t : Nat) (v w : Nat → Sig) (r s : Row) (d p : Nat)
    (e : ∀ j<d, bit r (v j)=bit s (w j)) :
    bit r (motifEval t v d p)=bit s (motifEval t w d p) := by
  induction d generalizing p with
  | zero => simp only [motifEval];split <;> simp [bit_one,bit_zero]
  | succ d ih =>
    have eqd := e d (by omega)
    have small : ∀ j<d, bit r (v j)=bit s (w j) := fun j hj => e j (by omega)
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
  if 65536 ≤ m then motifEval (m >>> 16) x 4 0 else
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

def kwCodes (i : Nat) : Nat := (if i < 1 then 0x111040220210850211104022021084e611104022021084e211104022021084de11104022021084c211104022021084a21110402202108482111040220200850211104022020084c211104012061085221110400602108522111040020210852a11104002021085261110400202108522111040020210851e11104002021084e611104002021084e211104002021084de111040020210849e111040020210849a10c21104080921ce10c080c208288a0610c080c2082889e210c080c2082889c610c080c2082889c210c080c20828898610c080c20828890610c080c20828888210c08042080889c610c080420808894610c080420800890210a13012082a81da10a13002082a81d610a111028829216210a111028829215e10a11002002a821a10a11002002a81d610a100c4040911ca1092081011010416109208009141040e1092080011410612109208001141060e10920800114105d210920800114104161092080011410412109208001141040e10910c005121041210910c001121065610910c001121061610910c001121061210910c00112105d210910c001121058e10910c001121041210910c001121040e109108181921041a1091081019210616109108101921042a10910810192104261091081019210422109108101921041e109108101921041a10910810192104161091081019010412109108101121041a1091081011210416109108101121041210910810110104161091080819210416109108081121041a109108081121041610910800916104161091080091610412109108005921041610910800512104161091080051210412109108001921041a10910800192104161091080011610412109108001161040e10910800112106621091080011210656109108001121061e109108001121061610910800112105e210910800112105d210910800112104261091080011210422109108001121041e109108001121041a1091080011210416109108001121041210910800110104161091080011010412109108000121069610910800012106561091080001210616109108000121061200000000000c0b0400000000000c02100000000000092190000000000009050000000000000900880000000000090084000000000008221000000000000821100000000000080904000000000008088400000000000801040000000000060280000000000006011000000000000409040000000000040884000000000003012000000000000210880000000000012110000000000001058000000000000101200000000000010110000000000000611000000000000049040000000000002904000000000000288400000000000016080000000000000c840000000000000984000000000000052000000000000005000000000000000110 else (if i < 2 then 0x222810004302125a22281000430210a6222810004302109e222810004302109a2228100043021096222810004302105a22281000430210562228100043021052222810004302104e222418004282125a222410124282109e222410104282109e222410104282109a222410024382129a22241002438210aa22241002438210a6222410024382109e222410024382109a222410024382105a222410024282125a22241002428210aa222410024282109e222410024282109a222410024282105a222410014282109a222410006292105a222410004382109a222410004282129a222410004282125a22241000428210aa22241000428210a6222410004282109e222410004282109a2224100042821096222410004282105a2224100042821052222410000282125620c211040c09220e20c211040c0921ce20c211040c09214e20c201040809218e20c201040809214a20a80c001600840e20a804001600841620a804001600841220a120840c09118a20a120840c09114a20a120840c09114620a120840c01114620a101a40449110620a101840441108220a100c60409110a20a100c40419118620a100c40419110a20a100c4040911c620a100a40409110620a100840c0110c220a100840409118a20a100840409114a20a100840409114620a100840409110a20a100840409110620a100840401114620a10084040110c220a100040409116a20a100040409116620a1000404091122115020042304085a11422000616408661142200021440862114220002144085e1142200021440856114220002104085e114220002104085a11241806029282961124180602928252112418060292821611241806029281d21124180202928296111070220610854211106022061085421110602202108682111060220210860211106022021085421110602202108522111060220210850211106022021084c211105062061084c211105022061086421110502206108602111050220610854211105022061085261110502206108522111050220610850211105022021085421110502202108522111050220210850211105022021084de11105022021084c2111040a202108502111040a2021084de111040a2021084c2111040620210850211104062021084c211104026021085e2111040260210852211104026021084e211104023029084e21110402206108602111040220610854211104022061085261110402206108522111040220610850211104022061084de111040220290850211104022021086821110402202108642111040220210861e111040220210860211104022021085e611104022021085c211104022021085a611104022021085821110402202108542111040220210852a11104022021085261110402202108522111040220210851e else 0xa018885003040a06a0188850030409c6a0188850030409c2841108100065010a812402100414421281240210041441ce812402100414418e811211100614220e811201100214220e81120110021421ce811201100214218e811201100214214a81104818041d019281104810001d0192504080420c0088c250190488030211ca48088c0c0292829648088c0c0292825e48088c0c0292825248088c0c0292821a48088c0c029281d648088c0c0292819648088c0c0292819248088c0c0292815248088c08029282524808840c02928192480884080092814e425008104c011052425008004c01100e42440208082241d2424402080822418e424088420c008946420884088072814e420884082032810a420884080032814e420884080032810e420884080032810a42088408003280ca42086418082a825e42086408082a821242084508802a819242084408203280c642084408002a81d642084408002a819242084408002a815242084408002a814e42084408002a810a42084408002a80c624502008860420e2245020088604209e245020008204209a24442002838420e22440a0088614225e2440a0008214225e242101c40451110624210184245111062421018404411106242100c4045111c6242100c4045111062421008404411146242100840441110624210084044110c624210084044110c2242100840401114a242100840401110a24210084040110c62244240601a5025a2244240601a281e2224205040921218e224205040921214e224205040921214a224205040921210a224205040901214a22420404092121262228180043021216222818004302109a2228100243021056))
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
  | two d h ha hb ih => cases d <;> exact Reach.two _ ih (availMap f ha) (availMap f hb)
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
theorem samples11008 (r : Row) : List.ofFn (sample11008 r) = (vars 511).map (bit r) := by
  rw [←raw11008,List.map_ofFn]
  rfl
theorem edge11008_table : ∀ r : Row, bit r (graphGoal 511) = edge11008 (sample11008 r) := by decide +kernel

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
    rw [←b_read,execute_bits _ _ _ (fun g hg => (hf g hg).1),←samples11008,edge11008_table]
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
def packed3907518471r3 (i : Nat) : Nat := 0x7
def layer3907518471r3 : Packing := (1,0,0,63,0,0,1,packed3907518471r3)
def samples3907518471 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0ff,0x2222),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f,0x4444),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8888),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols3907518471 : IndexTree ColumnInfo := (.leaf [])
def levels3907518471 : Nat → Packing
  | 3 => layer3907518471r3
  | _ => emptyPacking
def index3907518471 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g3907518471 : Forest := ⟨3907518471,3,fun j => samples3907518471[j]?.getD (0,0),cols3907518471,#[[]],levels3907518471,index3907518471,noFactory,noFactorySound 3907518471⟩
def packed2298085391r3 (i : Nat) : Nat := 0x5e33
def layer2298085391r3 : Packing := (1,1,0,63,0,0,1,packed2298085391r3)
def keys2298085391k4 (i : Nat) : Nat := 0x8
def packed2298085391r4 (i : Nat) : Nat := 0x20f
def layer2298085391r4 : Packing := (1,0,0,63,0,0,1,packed2298085391r4)
def samples2298085391 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ffff,0x4848484848484848),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ff00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9292929292929292),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffffff0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0e0e0e0e0e0e0e0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfc),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols2298085391 : IndexTree ColumnInfo := (.leaf [])
def levels2298085391 : Nat → Packing
  | 3 => layer2298085391r3
  | 4 => layer2298085391r4
  | _ => emptyPacking
def index2298085391 : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 4 0 0 keys2298085391k4
  | _ => fun _ => none
def g2298085391 : Forest := ⟨2298085391,4,fun j => samples2298085391[j]?.getD (0,0),cols2298085391,#[[]],levels2298085391,index2298085391,noFactory,noFactorySound 2298085391⟩
def packed2391670791r3 (i : Nat) : Nat := 0x930c0f88ae22d847a00
def layer2391670791r3 : Packing := (4,1,0,63,0,5,1,packed2391670791r3)
def keys2391670791k4 (i : Nat) : Nat := 0x94000b00003a000
def packed2391670791r4 (i : Nat) : Nat := 0x107
def layer2391670791r4 : Packing := (1,0,0,63,0,0,1,packed2391670791r4)
def samples2391670791 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f,0x4444),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8888),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeeee),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols2391670791 : IndexTree ColumnInfo := (.leaf [])
def levels2391670791 : Nat → Packing
  | 3 => layer2391670791r3
  | 4 => layer2391670791r4
  | _ => emptyPacking
def index2391670791 : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 11 0 6 2 0 keys2391670791k4
  | _ => fun _ => none
def g2391670791 : Forest := ⟨2391670791,4,fun j => samples2391670791[j]?.getD (0,0),cols2391670791,#[[]],levels2391670791,index2391670791,noFactory,noFactorySound 2391670791⟩
def packed2834038799r3 (i : Nat) : Nat := 0x5e33
def layer2834038799r3 : Packing := (1,1,0,63,0,0,1,packed2834038799r3)
def keys2834038799k4 (i : Nat) : Nat := 0x8
def packed2834038799r4 (i : Nat) : Nat := 0x20f
def layer2834038799r4 : Packing := (1,0,0,63,0,0,1,packed2834038799r4)
def samples2834038799 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffff00,0x1212121212121212),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff00ffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa0a0a0a0a0a0a0a0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffff0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc4c4c4c4c4c4c4c4),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8f8f8f8f8f8f8f8),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols2834038799 : IndexTree ColumnInfo := (.leaf [])
def levels2834038799 : Nat → Packing
  | 3 => layer2834038799r3
  | 4 => layer2834038799r4
  | _ => emptyPacking
def index2834038799 : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 4 0 0 keys2834038799k4
  | _ => fun _ => none
def g2834038799 : Forest := ⟨2834038799,4,fun j => samples2834038799[j]?.getD (0,0),cols2834038799,#[[]],levels2834038799,index2834038799,noFactory,noFactorySound 2834038799⟩
def packed185270279r3 (i : Nat) : Nat := 0x7
def layer185270279r3 : Packing := (1,0,0,63,0,0,1,packed185270279r3)
def samples185270279 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd294),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe739),(0x0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbde),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols185270279 : IndexTree ColumnInfo := (.leaf [])
def levels185270279 : Nat → Packing
  | 3 => layer185270279r3
  | _ => emptyPacking
def index185270279 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g185270279 : Forest := ⟨185270279,3,fun j => samples185270279[j]?.getD (0,0),cols185270279,#[[]],levels185270279,index185270279,noFactory,noFactorySound 185270279⟩
def packed791609351r3 (i : Nat) : Nat := 0x7
def layer791609351r3 : Packing := (1,0,0,63,0,0,1,packed791609351r3)
def samples791609351 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe38,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc924),(0xfc0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffedb6),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols791609351 : IndexTree ColumnInfo := (.leaf [])
def levels791609351 : Nat → Packing
  | 3 => layer791609351r3
  | _ => emptyPacking
def index791609351 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g791609351 : Forest := ⟨791609351,3,fun j => samples791609351[j]?.getD (0,0),cols791609351,#[[]],levels791609351,index791609351,noFactory,noFactorySound 791609351⟩
def packed3907649551r2 (i : Nat) : Nat := 0x930c086a908119c5544408ce2aa3222650d5291131
def layer3907649551r2 : Packing := (4,3,0,63,0,5,1,packed3907649551r2)
def keys3907649551k3 (i : Nat) : Nat := 0xbb90002f4
def packed3907649551r3 (i : Nat) : Nat := 0x2082082083d8930c09d428ce7506339c408ce7911329e444c6791030
def layer3907649551r3 : Packing := (6,2,0,63,0,5,1,packed3907649551r3)
def keys3907649551k4 (i : Nat) : Nat := 0x188000da60000560000001f2880
def packed3907649551r4 (i : Nat) : Nat := 0x820820820820aa479848c180fc6778cee996e22ba63d846e187a00
def layer3907649551r4 : Packing := (8,1,0,63,0,6,1,packed3907649551r4)
def keys3907649551k5 (i : Nat) : Nat := 0x19000000d94000640000000c60000000000003e03c46
def packed3907649551r5 (i : Nat) : Nat := 0x20f
def layer3907649551r5 : Packing := (1,0,0,63,0,0,1,packed3907649551r5)
def samples3907649551 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff01fffff01fffff,0x1020408102040810),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe03ffffe03f80,0x2244891224489122),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc07ffffc000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc489122448912244),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8f1e3c78f1e3c78),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols3907649551 : IndexTree ColumnInfo := (.leaf [])
def levels3907649551 : Nat → Packing
  | 2 => layer3907649551r2
  | 3 => layer3907649551r3
  | 4 => layer3907649551r4
  | 5 => layer3907649551r5
  | _ => emptyPacking
def index3907649551 : Nat → Nat → Option (Nat × Nat)
  | 3 => lookupWord 1 8 0 6 2 0 keys3907649551k3
  | 4 => lookupWord 2 20 0 7 3 0 keys3907649551k4
  | 5 => lookupWord 2 25 0 7 3 0 keys3907649551k5
  | _ => fun _ => none
def g3907649551 : Forest := ⟨3907649551,5,fun j => samples3907649551[j]?.getD (0,0),cols3907649551,#[[]],levels3907649551,index3907649551,noFactory,noFactorySound 3907649551⟩
def packed724238343r3 (i : Nat) : Nat := 0x61548f30918301d88a11dc4508d83048729084364c021cc4508da33803511401c84600
def layer724238343r3 : Packing := (9,2,0,63,0,6,1,packed724238343r3)
def keys724238343k4 (i : Nat) : Nat := 0x21000000a200005300004000c600c70000000000a475000000000000000000000000001800
def packed724238343r4 (i : Nat) : Nat := 0x82082082082082082084f1b305490f182430300f88bd21f087e11f483c20f443c10f802e22d847a00
def layer724238343r4 : Packing := (12,1,0,63,0,7,1,packed724238343r4)
def keys724238343k5 (i : Nat) : Nat := 0x9200000053000000000000889100340000000000f9003500060000000000006a0be700000000c00020
def packed724238343r5 (i : Nat) : Nat := 0x107
def layer724238343r5 : Packing := (1,0,0,63,0,0,1,packed724238343r5)
def samples724238343 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8888),(0xf00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdddd),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeeee),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols724238343 : IndexTree ColumnInfo := (.leaf [])
def levels724238343 : Nat → Packing
  | 3 => layer724238343r3
  | 4 => layer724238343r4
  | 5 => layer724238343r5
  | _ => emptyPacking
def index724238343 : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 3 37 0 8 4 0 keys724238343k4
  | 5 => lookupWord 4 44 2 8 4 0 keys724238343k5
  | _ => fun _ => none
def g724238343 : Forest := ⟨724238343,5,fun j => samples724238343[j]?.getD (0,0),cols724238343,#[[]],levels724238343,index724238343,noFactory,noFactorySound 724238343⟩
def packed3909025807r2 (i : Nat) : Nat := 0x63061509418cf1284a0467914150233
def layer3909025807r2 : Packing := (3,3,0,63,0,4,1,packed3909025807r2)
def keys3909025807k3 (i : Nat) : Nat := 0x10000f42000
def packed3909025807r3 (i : Nat) : Nat := 0x2082082083d8930c0cd428cf550633d9408cf38cc32d6330c768cc30
def layer3909025807r3 : Packing := (6,2,0,63,0,5,1,packed3909025807r3)
def keys3909025807k4 (i : Nat) : Nat := 0x1601e8000c6a780089
def packed3909025807r4 (i : Nat) : Nat := 0x820820820820aa479848c180fc6778cf6196e22e863d847c187a00
def layer3909025807r4 : Packing := (8,1,0,63,0,6,1,packed3909025807r4)
def keys3909025807k5 (i : Nat) : Nat := 0x1c00040158000de03ccd96000628
def packed3909025807r5 (i : Nat) : Nat := 0x20f
def layer3909025807r5 : Packing := (1,0,0,63,0,0,1,packed3909025807r5)
def samples3909025807 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0fff0f0f0f0,0x222222222222),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0fff00ff00,0x444444444444),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0ffff0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff888888888888),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols3909025807 : IndexTree ColumnInfo := (.leaf [])
def levels3909025807 : Nat → Packing
  | 2 => layer3909025807r2
  | 3 => layer3909025807r3
  | 4 => layer3909025807r4
  | 5 => layer3909025807r5
  | _ => emptyPacking
def index3909025807 : Nat → Nat → Option (Nat × Nat)
  | 3 => lookupWord 1 11 0 6 2 0 keys3909025807k3
  | 4 => lookupWord 2 11 1 7 3 0 keys3909025807k4
  | 5 => lookupWord 2 19 2 7 3 0 keys3909025807k5
  | _ => fun _ => none
def g3909025807 : Forest := ⟨3909025807,5,fun j => samples3909025807[j]?.getD (0,0),cols3909025807,#[[]],levels3909025807,index3909025807,noFactory,noFactorySound 3909025807⟩
def packed183369743r3 (i : Nat) : Nat := 0x338ce22
def layer183369743r3 : Packing := (1,2,0,63,0,0,1,packed183369743r3)
def keys183369743k4 (i : Nat) : Nat := 0x3
def packed183369743r4 (i : Nat) : Nat := 0x820820820820aa479848c180bc67b0cb7117531ec23b083a887a00
def layer183369743r4 : Packing := (8,1,0,63,0,6,1,packed183369743r4)
def keys183369743k5 (i : Nat) : Nat := 0x2a0001d447afe00000007800092000000000000004c0000000000
def packed183369743r5 (i : Nat) : Nat := 0x20f
def layer183369743r5 : Packing := (1,0,0,63,0,0,1,packed183369743r5)
def samples183369743 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffff00ff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa0a0a0a0a0a0a0a0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffff00ffff00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8c8c8c8c8c8c8c8),(0xffffff000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2f2f2f2f2f2f2f2),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfc),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols183369743 : IndexTree ColumnInfo := (.leaf [])
def levels183369743 : Nat → Packing
  | 3 => layer183369743r3
  | 4 => layer183369743r4
  | 5 => layer183369743r5
  | _ => emptyPacking
def index183369743 : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 4 0 0 keys183369743k4
  | 5 => lookupWord 2 31 0 7 3 0 keys183369743k5
  | _ => fun _ => none
def g183369743 : Forest := ⟨183369743,5,fun j => samples183369743[j]?.getD (0,0),cols183369743,#[[]],levels183369743,index183369743,noFactory,noFactorySound 183369743⟩
def packed181338127r3 (i : Nat) : Nat := 0x338ce22
def layer181338127r3 : Packing := (1,2,0,63,0,0,1,packed181338127r3)
def keys181338127k4 (i : Nat) : Nat := 0x3
def packed181338127r4 (i : Nat) : Nat := 0x820820820820aa479848c180bc67b88ba98f421ec23e0c3c907a00
def layer181338127r4 : Packing := (8,1,0,63,0,6,1,packed181338127r4)
def keys181338127k5 (i : Nat) : Nat := 0x6399a5b0000000e55c0287a0000000000000002
def packed181338127r5 (i : Nat) : Nat := 0x20f
def layer181338127r5 : Packing := (1,0,0,63,0,0,1,packed181338127r5)
def samples181338127 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa2a2a2a2a2a2a2a2),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffffff0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8c8c8c8c8c8c8c8),(0xffff00000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3f3f3f3f3f3f3f3),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfc),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols181338127 : IndexTree ColumnInfo := (.leaf [])
def levels181338127 : Nat → Packing
  | 3 => layer181338127r3
  | 4 => layer181338127r4
  | 5 => layer181338127r5
  | _ => emptyPacking
def index181338127 : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 4 0 0 keys181338127k4
  | 5 => lookupWord 2 22 1 7 3 0 keys181338127k5
  | _ => fun _ => none
def g181338127 : Forest := ⟨181338127,5,fun j => samples181338127[j]?.getD (0,0),cols181338127,#[[]],levels181338127,index181338127,noFactory,noFactorySound 181338127⟩
def packed2328756239r3 (i : Nat) : Nat := 0x338ce22
def layer2328756239r3 : Packing := (1,2,0,63,0,0,1,packed2328756239r3)
def keys2328756239k4 (i : Nat) : Nat := 0x3
def packed2328756239r4 (i : Nat) : Nat := 0x820820820820aa479848c180bc67b88ae18ed21ec2374c36107a00
def layer2328756239r4 : Packing := (8,1,0,63,0,6,1,packed2328756239r4)
def keys2328756239k5 (i : Nat) : Nat := 0x560000020000000001b690000000007800cb700000730000000
def packed2328756239r5 (i : Nat) : Nat := 0x20f
def layer2328756239r5 : Packing := (1,0,0,63,0,0,1,packed2328756239r5)
def samples2328756239 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00ff,0x4444444444444444),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffffffff00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9090909090909090),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffff000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe6e6e6e6e6e6e6e6),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8f8f8f8f8f8f8f8),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols2328756239 : IndexTree ColumnInfo := (.leaf [])
def levels2328756239 : Nat → Packing
  | 3 => layer2328756239r3
  | 4 => layer2328756239r4
  | 5 => layer2328756239r5
  | _ => emptyPacking
def index2328756239 : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 4 0 0 keys2328756239k4
  | 5 => lookupWord 2 32 0 7 3 0 keys2328756239k5
  | _ => fun _ => none
def g2328756239 : Forest := ⟨2328756239,5,fun j => samples2328756239[j]?.getD (0,0),cols2328756239,#[[]],levels2328756239,index2328756239,noFactory,noFactorySound 2328756239⟩
def packed2293170191r3 (i : Nat) : Nat := 0x338ce22
def layer2293170191r3 : Packing := (1,2,0,63,0,0,1,packed2293170191r3)
def keys2293170191k4 (i : Nat) : Nat := 0x3
def packed2293170191r4 (i : Nat) : Nat := 0x820820820820aa479848c180bc67b4cb7117431ec23b483a087a00
def layer2293170191r4 : Packing := (8,1,0,63,0,6,1,packed2293170191r4)
def keys2293170191k5 (i : Nat) : Nat := 0x19000060096000650003b00000000000880000003c47
def packed2293170191r5 (i : Nat) : Nat := 0x20f
def layer2293170191r5 : Packing := (1,0,0,63,0,0,1,packed2293170191r5)
def samples2293170191 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff00,0x4848484848484848),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffff0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9292929292929292),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ffff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe3e3e3e3e3e3e3e3),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcfcfcfcfcfcfcfc),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols2293170191 : IndexTree ColumnInfo := (.leaf [])
def levels2293170191 : Nat → Packing
  | 3 => layer2293170191r3
  | 4 => layer2293170191r4
  | 5 => layer2293170191r5
  | _ => emptyPacking
def index2293170191 : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 4 0 0 keys2293170191k4
  | 5 => lookupWord 2 25 0 7 3 0 keys2293170191k5
  | _ => fun _ => none
def g2293170191 : Forest := ⟨2293170191,5,fun j => samples2293170191[j]?.getD (0,0),cols2293170191,#[[]],levels2293170191,index2293170191,noFactory,noFactorySound 2293170191⟩
def packed774766599r3 (i : Nat) : Nat := 0x7
def layer774766599r3 : Packing := (1,0,0,63,0,0,1,packed774766599r3)
def samples774766599 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8888),(0xff0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccc),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeeee),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols774766599 : IndexTree ColumnInfo := (.leaf [])
def levels774766599 : Nat → Packing
  | 3 => layer774766599r3
  | _ => emptyPacking
def index774766599 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g774766599 : Forest := ⟨774766599,3,fun j => samples774766599[j]?.getD (0,0),cols774766599,#[[]],levels774766599,index774766599,noFactory,noFactorySound 774766599⟩
def packed2896953351r3 (i : Nat) : Nat := 0x7
def layer2896953351r3 : Packing := (1,0,0,63,0,0,1,packed2896953351r3)
def samples2896953351 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0,0x2222),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0ff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8888),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcccc),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols2896953351 : IndexTree ColumnInfo := (.leaf [])
def levels2896953351 : Nat → Packing
  | 3 => layer2896953351r3
  | _ => emptyPacking
def index2896953351 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g2896953351 : Forest := ⟨2896953351,3,fun j => samples2896953351[j]?.getD (0,0),cols2896953351,#[[]],levels2896953351,index2896953351,noFactory,noFactorySound 2896953351⟩
def packed2576941059r2 (i : Nat) : Nat := 0xc2c23a00
def layer2576941059r2 : Packing := (2,1,0,63,0,3,1,packed2576941059r2)
def keys2576941059k3 (i : Nat) : Nat := 0x15c0
def packed2576941059r3 (i : Nat) : Nat := 0x83
def layer2576941059r3 : Packing := (1,0,0,63,0,0,1,packed2576941059r3)
def samples2576941059 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc,0x5),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols2576941059 : IndexTree ColumnInfo := (.leaf [])
def levels2576941059 : Nat → Packing
  | 2 => layer2576941059r2
  | 3 => layer2576941059r3
  | _ => emptyPacking
def index2576941059 : Nat → Nat → Option (Nat × Nat)
  | 3 => lookupWord 1 5 0 5 1 0 keys2576941059k3
  | _ => fun _ => none
def g2576941059 : Forest := ⟨2576941059,3,fun j => samples2576941059[j]?.getD (0,0),cols2576941059,#[[]],levels2576941059,index2576941059,noFactory,noFactorySound 2576941059⟩
def packed3941335055r4 (i : Nat) : Nat := 0xf624c303f19de33ba65b88bb08fa00
def layer3941335055r4 : Packing := (6,1,0,63,0,5,1,packed3941335055r4)
def keys3941335055k5 (i : Nat) : Nat := 0xb92000620000000000000000000003a03c44
def packed3941335055r5 (i : Nat) : Nat := 0x20f
def layer3941335055r5 : Packing := (1,0,0,63,0,0,1,packed3941335055r5)
def samples3941335055 : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ffffff03ffc0,0x82082082082082),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff03f03ffc0fff,0x410410410410410),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc003ffff000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff924924924924924),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe38e38e38e38e38),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols3941335055 : IndexTree ColumnInfo := (.leaf [])
def levels3941335055 : Nat → Packing
  | 4 => layer3941335055r4
  | 5 => layer3941335055r5
  | _ => emptyPacking
def index3941335055 : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 2 25 0 7 3 0 keys3941335055k5
  | _ => fun _ => none
def g3941335055 : Forest := ⟨3941335055,5,fun j => samples3941335055[j]?.getD (0,0),cols3941335055,#[[]],levels3941335055,index3941335055,noFactory,noFactorySound 3941335055⟩
def packed4009230351r3 (i : Nat) : Nat := 0x30ac428cf38cd32
def layer4009230351r3 : Packing := (2,2,0,63,0,3,1,packed4009230351r3)
def keys4009230351k4 (i : Nat) : Nat := 0x301b
def packed4009230351r4 (i : Nat) : Nat := 0x820820820f624c303f19de33da65b88bb08fa00
def layer4009230351r4 : Packing := (6,1,0,63,0,5,1,packed4009230351r4)
def keys4009230351k5 (i : Nat) : Nat := 0x1c00020150000da00000006c061
def packed4009230351r5 (i : Nat) : Nat := 0x20f
def layer4009230351r5 : Packing := (1,0,0,63,0,0,1,packed4009230351r5)
def samples4009230351 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1ff83ff07c1f,0x8421084210842),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0ffc1ff801f,0x10842108421084),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0001ffffe0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc2108421084210),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe318c6318c6318),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols4009230351 : IndexTree ColumnInfo := (.leaf [])
def levels4009230351 : Nat → Packing
  | 3 => layer4009230351r3
  | 4 => layer4009230351r4
  | 5 => layer4009230351r5
  | _ => emptyPacking
def index4009230351 : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 3 0 5 1 0 keys4009230351k4
  | 5 => lookupWord 2 19 0 7 3 0 keys4009230351k5
  | _ => fun _ => none
def g4009230351 : Forest := ⟨4009230351,5,fun j => samples4009230351[j]?.getD (0,0),cols4009230351,#[[]],levels4009230351,index4009230351,noFactory,noFactorySound 4009230351⟩
def packed1717960707r2 (i : Nat) : Nat := 0x3
def layer1717960707r2 : Packing := (1,0,0,63,0,0,1,packed1717960707r2)
def samples1717960707 : Array (Bits × Bits) := #[(0x3,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols1717960707 : IndexTree ColumnInfo := (.leaf [])
def levels1717960707 : Nat → Packing
  | 2 => layer1717960707r2
  | _ => emptyPacking
def index1717960707 : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g1717960707 : Forest := ⟨1717960707,2,fun j => samples1717960707[j]?.getD (0,0),cols1717960707,#[[]],levels1717960707,index1717960707,noFactory,noFactorySound 1717960707⟩
def packed2901278735r4 (i : Nat) : Nat := 0xc498605e33d865b88bb08fa00
def layer2901278735r4 : Packing := (5,1,0,63,0,5,1,packed2901278735r4)
def keys2901278735k5 (i : Nat) : Nat := 0x341300005000001641
def packed2901278735r5 (i : Nat) : Nat := 0x20f
def layer2901278735r5 : Packing := (1,0,0,63,0,0,1,packed2901278735r5)
def samples2901278735 : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0fc0fff03f,0x208208208208208),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ffffff03ffc0,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff820820820820820),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000ffffc0000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcb2cb2cb2cb2cb2),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff3cf3cf3cf3cf3c),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def cols2901278735 : IndexTree ColumnInfo := (.leaf [])
def levels2901278735 : Nat → Packing
  | 4 => layer2901278735r4
  | 5 => layer2901278735r5
  | _ => emptyPacking
def index2901278735 : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 19 0 7 3 0 keys2901278735k5
  | _ => fun _ => none
def g2901278735 : Forest := ⟨2901278735,5,fun j => samples2901278735[j]?.getD (0,0),cols2901278735,#[[]],levels2901278735,index2901278735,noFactory,noFactorySound 2901278735⟩
theorem geom3907518471 : graphValid g3907518471 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice3907518471k3p0 : mixedBlock g3907518471 3 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK3907518471k3 : mixedBlock g3907518471 3 0 1 := slice3907518471k3p0
theorem checked3907518471 : mixedTables g3907518471 3 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g3907518471 0 0)
  · exact (mixedEmpty g3907518471 1 0)
  · exact (mixedEmpty g3907518471 2 0)
  · exact layerOK3907518471k3
def support3907518471 : List (Sig × Row × Row) := [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,1,5)]
theorem low3907518471 : Lower (vars 3907518471) (graphGoal 3907518471) 4 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g3907518471) (before_sound [] baseKnown) geom3907518471 checked3907518471 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 3907518471) (vars 3907518471) support3907518471=true := by decide +kernel
  apply essential_ok h a
  have e : support3907518471.map Prod.fst = vars 3907518471 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule0 : PlaneRule := ⟨[43690,52428,61680],59624,4,liftPlane low3907518471 (by decide +kernel) (by decide +kernel),properPlane (p:=3) (n:=0) (by decide) (by decide)⟩
theorem geom2298085391 : graphValid g2298085391 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice2298085391k3p0 : mixedBlock g2298085391 3 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2298085391k3 : mixedBlock g2298085391 3 0 1 := slice2298085391k3p0
theorem slice2298085391k4p0 : mixedBlock g2298085391 4 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2298085391k4 : mixedBlock g2298085391 4 0 1 := slice2298085391k4p0
theorem checked2298085391 : mixedTables g2298085391 4 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g2298085391 0 0)
  · exact (mixedEmpty g2298085391 1 0)
  · exact (mixedEmpty g2298085391 2 0)
  · exact layerOK2298085391k3
  · exact layerOK2298085391k4
def support2298085391 : List (Sig × Row × Row) := [(inputs.getD 0 zero,0,1),(inputs.getD 1 zero,9,11),(inputs.getD 2 zero,0,4),(inputs.getD 3 zero,1,9)]
theorem low2298085391 : Lower (vars 2298085391) (graphGoal 2298085391) 5 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g2298085391) (before_sound [] baseKnown) geom2298085391 checked2298085391 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 2298085391) (vars 2298085391) support2298085391=true := by decide +kernel
  apply essential_ok h a
  have e : support2298085391.map Prod.fst = vars 2298085391 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule1 : PlaneRule := ⟨[43690,52428,61680,65280],35066,5,liftPlane low2298085391 (by decide +kernel) (by decide +kernel),properPlane (p:=1) (n:=0) (by decide) (by decide)⟩
theorem geom2391670791 : graphValid g2391670791 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice2391670791k3p0 : mixedBlock g2391670791 3 0 3 := by
  apply mixedVerified
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem slice2391670791k3p3 : mixedBlock g2391670791 3 3 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2391670791k3 : mixedBlock g2391670791 3 0 4 := (@mixedJoin g2391670791 3 0 3 1 slice2391670791k3p0 slice2391670791k3p3)
theorem slice2391670791k4p0 : mixedBlock g2391670791 4 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2391670791k4 : mixedBlock g2391670791 4 0 1 := slice2391670791k4p0
theorem checked2391670791 : mixedTables g2391670791 4 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g2391670791 0 0)
  · exact (mixedEmpty g2391670791 1 0)
  · exact (mixedEmpty g2391670791 2 0)
  · exact layerOK2391670791k3
  · exact layerOK2391670791k4
def support2391670791 : List (Sig × Row × Row) := [(inputs.getD 0 zero,0,1),(inputs.getD 1 zero,0,2),(inputs.getD 2 zero,1,5)]
theorem low2391670791 : Lower (vars 2391670791) (graphGoal 2391670791) 5 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g2391670791) (before_sound [] baseKnown) geom2391670791 checked2391670791 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 2391670791) (vars 2391670791) support2391670791=true := by decide +kernel
  apply essential_ok h a
  have e : support2391670791.map Prod.fst = vars 2391670791 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule2 : PlaneRule := ⟨[43690,52428,61680],36494,5,liftPlane low2391670791 (by decide +kernel) (by decide +kernel),properPlane (p:=1) (n:=0) (by decide) (by decide)⟩
theorem geom2834038799 : graphValid g2834038799 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice2834038799k3p0 : mixedBlock g2834038799 3 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2834038799k3 : mixedBlock g2834038799 3 0 1 := slice2834038799k3p0
theorem slice2834038799k4p0 : mixedBlock g2834038799 4 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2834038799k4 : mixedBlock g2834038799 4 0 1 := slice2834038799k4p0
theorem checked2834038799 : mixedTables g2834038799 4 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g2834038799 0 0)
  · exact (mixedEmpty g2834038799 1 0)
  · exact (mixedEmpty g2834038799 2 0)
  · exact layerOK2834038799k3
  · exact layerOK2834038799k4
def support2834038799 : List (Sig × Row × Row) := [(inputs.getD 0 zero,4,5),(inputs.getD 1 zero,0,2),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,2,10)]
theorem low2834038799 : Lower (vars 2834038799) (graphGoal 2834038799) 5 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g2834038799) (before_sound [] baseKnown) geom2834038799 checked2834038799 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 2834038799) (vars 2834038799) support2834038799=true := by decide +kernel
  apply essential_ok h a
  have e : support2834038799.map Prod.fst = vars 2834038799 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule3 : PlaneRule := ⟨[43690,52428,61680,65280],43244,5,liftPlane low2834038799 (by decide +kernel) (by decide +kernel),properPlane (p:=2) (n:=0) (by decide) (by decide)⟩
theorem geom185270279 : graphValid g185270279 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice185270279k3p0 : mixedBlock g185270279 3 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK185270279k3 : mixedBlock g185270279 3 0 1 := slice185270279k3p0
theorem checked185270279 : mixedTables g185270279 3 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g185270279 0 0)
  · exact (mixedEmpty g185270279 1 0)
  · exact (mixedEmpty g185270279 2 0)
  · exact layerOK185270279k3
def support185270279 : List (Sig × Row × Row) := [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,0,2),(inputs.getD 2 zero,0,4)]
theorem low185270279 : Lower (vars 185270279) (graphGoal 185270279) 4 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g185270279) (before_sound [] baseKnown) geom185270279 checked185270279 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 185270279) (vars 185270279) support185270279=true := by decide +kernel
  apply essential_ok h a
  have e : support185270279.map Prod.fst = vars 185270279 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule4 : PlaneRule := ⟨[43690,52428,61680],2827,4,liftPlane low185270279 (by decide +kernel) (by decide +kernel),properPlane (p:=0) (n:=2) (by decide) (by decide)⟩
theorem geom791609351 : graphValid g791609351 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice791609351k3p0 : mixedBlock g791609351 3 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK791609351k3 : mixedBlock g791609351 3 0 1 := slice791609351k3p0
theorem checked791609351 : mixedTables g791609351 3 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g791609351 0 0)
  · exact (mixedEmpty g791609351 1 0)
  · exact (mixedEmpty g791609351 2 0)
  · exact layerOK791609351k3
def support791609351 : List (Sig × Row × Row) := [(inputs.getD 0 zero,4,5),(inputs.getD 1 zero,5,7),(inputs.getD 2 zero,0,4)]
theorem low791609351 : Lower (vars 791609351) (graphGoal 791609351) 4 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g791609351) (before_sound [] baseKnown) geom791609351 checked791609351 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 791609351) (vars 791609351) support791609351=true := by decide +kernel
  apply essential_ok h a
  have e : support791609351.map Prod.fst = vars 791609351 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule5 : PlaneRule := ⟨[43690,52428,61680],12079,4,liftPlane low791609351 (by decide +kernel) (by decide +kernel),properPlane (p:=0) (n:=4) (by decide) (by decide)⟩
theorem geom3907649551 : graphValid g3907649551 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice3907649551k2p0 : mixedBlock g3907649551 2 0 4 := by
  apply mixedVerified
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK3907649551k2 : mixedBlock g3907649551 2 0 4 := slice3907649551k2p0
theorem slice3907649551k3p0 : mixedBlock g3907649551 3 0 6 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK3907649551k3 : mixedBlock g3907649551 3 0 6 := slice3907649551k3p0
theorem slice3907649551k4p0 : mixedBlock g3907649551 4 0 7 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem slice3907649551k4p7 : mixedBlock g3907649551 4 7 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK3907649551k4 : mixedBlock g3907649551 4 0 8 := (@mixedJoin g3907649551 4 0 7 1 slice3907649551k4p0 slice3907649551k4p7)
theorem slice3907649551k5p0 : mixedBlock g3907649551 5 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK3907649551k5 : mixedBlock g3907649551 5 0 1 := slice3907649551k5p0
theorem checked3907649551 : mixedTables g3907649551 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g3907649551 0 0)
  · exact (mixedEmpty g3907649551 1 0)
  · exact layerOK3907649551k2
  · exact layerOK3907649551k3
  · exact layerOK3907649551k4
  · exact layerOK3907649551k5
def support3907649551 : List (Sig × Row × Row) := [(inputs.getD 0 zero,0,1),(inputs.getD 1 zero,4,6),(inputs.getD 2 zero,2,6),(inputs.getD 3 zero,1,9)]
theorem low3907649551 : Lower (vars 3907649551) (graphGoal 3907649551) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g3907649551) (before_sound [] baseKnown) geom3907649551 checked3907649551 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 3907649551) (vars 3907649551) support3907649551=true := by decide +kernel
  apply essential_ok h a
  have e : support3907649551.map Prod.fst = vars 3907649551 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule6 : PlaneRule := ⟨[43690,52428,61680,65280],59626,6,liftPlane low3907649551 (by decide +kernel) (by decide +kernel),properPlane (p:=1) (n:=0) (by decide) (by decide)⟩
theorem geom724238343 : graphValid g724238343 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice724238343k3p0 : mixedBlock g724238343 3 0 7 := by
  apply mixedVerified
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem slice724238343k3p7 : mixedBlock g724238343 3 7 2 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK724238343k3 : mixedBlock g724238343 3 0 9 := (@mixedJoin g724238343 3 0 7 2 slice724238343k3p0 slice724238343k3p7)
theorem slice724238343k4p0 : mixedBlock g724238343 4 0 3 := by
  apply mixedVerified
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem slice724238343k4p3 : mixedBlock g724238343 4 3 9 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK724238343k4 : mixedBlock g724238343 4 0 12 := (@mixedJoin g724238343 4 0 3 9 slice724238343k4p0 slice724238343k4p3)
theorem slice724238343k5p0 : mixedBlock g724238343 5 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK724238343k5 : mixedBlock g724238343 5 0 1 := slice724238343k5p0
theorem checked724238343 : mixedTables g724238343 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g724238343 0 0)
  · exact (mixedEmpty g724238343 1 0)
  · exact (mixedEmpty g724238343 2 0)
  · exact layerOK724238343k3
  · exact layerOK724238343k4
  · exact layerOK724238343k5
def support724238343 : List (Sig × Row × Row) := [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,0,2),(inputs.getD 2 zero,0,4)]
theorem low724238343 : Lower (vars 724238343) (graphGoal 724238343) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g724238343) (before_sound [] baseKnown) geom724238343 checked724238343 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 724238343) (vars 724238343) support724238343=true := by decide +kernel
  apply essential_ok h a
  have e : support724238343.map Prod.fst = vars 724238343 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule7 : PlaneRule := ⟨[43690,52428,61680],11051,6,liftPlane low724238343 (by decide +kernel) (by decide +kernel),properPlane (p:=0) (n:=2) (by decide) (by decide)⟩
theorem geom3909025807 : graphValid g3909025807 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice3909025807k2p0 : mixedBlock g3909025807 2 0 3 := by
  apply mixedVerified
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK3909025807k2 : mixedBlock g3909025807 2 0 3 := slice3909025807k2p0
theorem slice3909025807k3p0 : mixedBlock g3909025807 3 0 6 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK3909025807k3 : mixedBlock g3909025807 3 0 6 := slice3909025807k3p0
theorem slice3909025807k4p0 : mixedBlock g3909025807 4 0 7 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem slice3909025807k4p7 : mixedBlock g3909025807 4 7 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK3909025807k4 : mixedBlock g3909025807 4 0 8 := (@mixedJoin g3909025807 4 0 7 1 slice3909025807k4p0 slice3909025807k4p7)
theorem slice3909025807k5p0 : mixedBlock g3909025807 5 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK3909025807k5 : mixedBlock g3909025807 5 0 1 := slice3909025807k5p0
theorem checked3909025807 : mixedTables g3909025807 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g3909025807 0 0)
  · exact (mixedEmpty g3909025807 1 0)
  · exact layerOK3909025807k2
  · exact layerOK3909025807k3
  · exact layerOK3909025807k4
  · exact layerOK3909025807k5
def support3909025807 : List (Sig × Row × Row) := [(inputs.getD 0 zero,10,11),(inputs.getD 1 zero,9,11),(inputs.getD 2 zero,9,13),(inputs.getD 3 zero,0,8)]
theorem low3909025807 : Lower (vars 3909025807) (graphGoal 3909025807) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g3909025807) (before_sound [] baseKnown) geom3909025807 checked3909025807 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 3909025807) (vars 3909025807) support3909025807=true := by decide +kernel
  apply essential_ok h a
  have e : support3909025807.map Prod.fst = vars 3909025807 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule8 : PlaneRule := ⟨[43690,52428,61680,65280],59647,6,liftPlane low3909025807 (by decide +kernel) (by decide +kernel),properPlane (p:=0) (n:=8) (by decide) (by decide)⟩
theorem geom183369743 : graphValid g183369743 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice183369743k3p0 : mixedBlock g183369743 3 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK183369743k3 : mixedBlock g183369743 3 0 1 := slice183369743k3p0
theorem slice183369743k4p0 : mixedBlock g183369743 4 0 8 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK183369743k4 : mixedBlock g183369743 4 0 8 := slice183369743k4p0
theorem slice183369743k5p0 : mixedBlock g183369743 5 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK183369743k5 : mixedBlock g183369743 5 0 1 := slice183369743k5p0
theorem checked183369743 : mixedTables g183369743 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g183369743 0 0)
  · exact (mixedEmpty g183369743 1 0)
  · exact (mixedEmpty g183369743 2 0)
  · exact layerOK183369743k3
  · exact layerOK183369743k4
  · exact layerOK183369743k5
def support183369743 : List (Sig × Row × Row) := [(inputs.getD 0 zero,0,1),(inputs.getD 1 zero,0,2),(inputs.getD 2 zero,9,13),(inputs.getD 3 zero,2,10)]
theorem low183369743 : Lower (vars 183369743) (graphGoal 183369743) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g183369743) (before_sound [] baseKnown) geom183369743 checked183369743 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 183369743) (vars 183369743) support183369743=true := by decide +kernel
  apply essential_ok h a
  have e : support183369743.map Prod.fst = vars 183369743 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule9 : PlaneRule := ⟨[43690,52428,61680,65280],2798,6,liftPlane low183369743 (by decide +kernel) (by decide +kernel),properPlane (p:=1) (n:=0) (by decide) (by decide)⟩
theorem geom181338127 : graphValid g181338127 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice181338127k3p0 : mixedBlock g181338127 3 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK181338127k3 : mixedBlock g181338127 3 0 1 := slice181338127k3p0
theorem slice181338127k4p0 : mixedBlock g181338127 4 0 8 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK181338127k4 : mixedBlock g181338127 4 0 8 := slice181338127k4p0
theorem slice181338127k5p0 : mixedBlock g181338127 5 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK181338127k5 : mixedBlock g181338127 5 0 1 := slice181338127k5p0
theorem checked181338127 : mixedTables g181338127 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g181338127 0 0)
  · exact (mixedEmpty g181338127 1 0)
  · exact (mixedEmpty g181338127 2 0)
  · exact layerOK181338127k3
  · exact layerOK181338127k4
  · exact layerOK181338127k5
def support181338127 : List (Sig × Row × Row) := [(inputs.getD 0 zero,8,9),(inputs.getD 1 zero,4,6),(inputs.getD 2 zero,0,4),(inputs.getD 3 zero,0,8)]
theorem low181338127 : Lower (vars 181338127) (graphGoal 181338127) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g181338127) (before_sound [] baseKnown) geom181338127 checked181338127 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 181338127) (vars 181338127) support181338127=true := by decide +kernel
  apply essential_ok h a
  have e : support181338127.map Prod.fst = vars 181338127 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule10 : PlaneRule := ⟨[43690,52428,61680,65280],2767,6,liftPlane low181338127 (by decide +kernel) (by decide +kernel),properPlane (p:=0) (n:=4) (by decide) (by decide)⟩
theorem geom2328756239 : graphValid g2328756239 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice2328756239k3p0 : mixedBlock g2328756239 3 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2328756239k3 : mixedBlock g2328756239 3 0 1 := slice2328756239k3p0
theorem slice2328756239k4p0 : mixedBlock g2328756239 4 0 8 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2328756239k4 : mixedBlock g2328756239 4 0 8 := slice2328756239k4p0
theorem slice2328756239k5p0 : mixedBlock g2328756239 5 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2328756239k5 : mixedBlock g2328756239 5 0 1 := slice2328756239k5p0
theorem checked2328756239 : mixedTables g2328756239 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g2328756239 0 0)
  · exact (mixedEmpty g2328756239 1 0)
  · exact (mixedEmpty g2328756239 2 0)
  · exact layerOK2328756239k3
  · exact layerOK2328756239k4
  · exact layerOK2328756239k5
def support2328756239 : List (Sig × Row × Row) := [(inputs.getD 0 zero,0,1),(inputs.getD 1 zero,0,2),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,2,10)]
theorem low2328756239 : Lower (vars 2328756239) (graphGoal 2328756239) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g2328756239) (before_sound [] baseKnown) geom2328756239 checked2328756239 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 2328756239) (vars 2328756239) support2328756239=true := by decide +kernel
  apply essential_ok h a
  have e : support2328756239.map Prod.fst = vars 2328756239 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule11 : PlaneRule := ⟨[43690,52428,61680,65280],35534,6,liftPlane low2328756239 (by decide +kernel) (by decide +kernel),properPlane (p:=1) (n:=0) (by decide) (by decide)⟩
theorem geom2293170191 : graphValid g2293170191 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice2293170191k3p0 : mixedBlock g2293170191 3 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2293170191k3 : mixedBlock g2293170191 3 0 1 := slice2293170191k3p0
theorem slice2293170191k4p0 : mixedBlock g2293170191 4 0 8 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2293170191k4 : mixedBlock g2293170191 4 0 8 := slice2293170191k4p0
theorem slice2293170191k5p0 : mixedBlock g2293170191 5 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2293170191k5 : mixedBlock g2293170191 5 0 1 := slice2293170191k5p0
theorem checked2293170191 : mixedTables g2293170191 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g2293170191 0 0)
  · exact (mixedEmpty g2293170191 1 0)
  · exact (mixedEmpty g2293170191 2 0)
  · exact layerOK2293170191k3
  · exact layerOK2293170191k4
  · exact layerOK2293170191k5
def support2293170191 : List (Sig × Row × Row) := [(inputs.getD 0 zero,4,5),(inputs.getD 1 zero,9,11),(inputs.getD 2 zero,0,4),(inputs.getD 3 zero,0,8)]
theorem low2293170191 : Lower (vars 2293170191) (graphGoal 2293170191) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g2293170191) (before_sound [] baseKnown) geom2293170191 checked2293170191 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 2293170191) (vars 2293170191) support2293170191=true := by decide +kernel
  apply essential_ok h a
  have e : support2293170191.map Prod.fst = vars 2293170191 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule12 : PlaneRule := ⟨[43690,52428,61680,65280],34991,6,liftPlane low2293170191 (by decide +kernel) (by decide +kernel),properPlane (p:=0) (n:=4) (by decide) (by decide)⟩
theorem geom774766599 : graphValid g774766599 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice774766599k3p0 : mixedBlock g774766599 3 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK774766599k3 : mixedBlock g774766599 3 0 1 := slice774766599k3p0
theorem checked774766599 : mixedTables g774766599 3 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g774766599 0 0)
  · exact (mixedEmpty g774766599 1 0)
  · exact (mixedEmpty g774766599 2 0)
  · exact layerOK774766599k3
def support774766599 : List (Sig × Row × Row) := [(inputs.getD 0 zero,0,1),(inputs.getD 1 zero,0,2),(inputs.getD 2 zero,2,6)]
theorem low774766599 : Lower (vars 774766599) (graphGoal 774766599) 4 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g774766599) (before_sound [] baseKnown) geom774766599 checked774766599 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 774766599) (vars 774766599) support774766599=true := by decide +kernel
  apply essential_ok h a
  have e : support774766599.map Prod.fst = vars 774766599 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule13 : PlaneRule := ⟨[43690,52428,61680],11822,4,liftPlane low774766599 (by decide +kernel) (by decide +kernel),properPlane (p:=1) (n:=0) (by decide) (by decide)⟩
theorem geom2896953351 : graphValid g2896953351 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice2896953351k3p0 : mixedBlock g2896953351 3 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2896953351k3 : mixedBlock g2896953351 3 0 1 := slice2896953351k3p0
theorem checked2896953351 : mixedTables g2896953351 3 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g2896953351 0 0)
  · exact (mixedEmpty g2896953351 1 0)
  · exact (mixedEmpty g2896953351 2 0)
  · exact layerOK2896953351k3
def support2896953351 : List (Sig × Row × Row) := [(inputs.getD 0 zero,4,5),(inputs.getD 1 zero,0,2),(inputs.getD 2 zero,1,5)]
theorem low2896953351 : Lower (vars 2896953351) (graphGoal 2896953351) 4 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g2896953351) (before_sound [] baseKnown) geom2896953351 checked2896953351 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 2896953351) (vars 2896953351) support2896953351=true := by decide +kernel
  apply essential_ok h a
  have e : support2896953351.map Prod.fst = vars 2896953351 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule14 : PlaneRule := ⟨[43690,52428,61680],44204,4,liftPlane low2896953351 (by decide +kernel) (by decide +kernel),properPlane (p:=2) (n:=0) (by decide) (by decide)⟩
theorem geom2576941059 : graphValid g2576941059 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice2576941059k2p0 : mixedBlock g2576941059 2 0 2 := by
  apply mixedVerified
  apply cellsBlock (ar:=2) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2576941059k2 : mixedBlock g2576941059 2 0 2 := slice2576941059k2p0
theorem slice2576941059k3p0 : mixedBlock g2576941059 3 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=2) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2576941059k3 : mixedBlock g2576941059 3 0 1 := slice2576941059k3p0
theorem checked2576941059 : mixedTables g2576941059 3 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g2576941059 0 0)
  · exact (mixedEmpty g2576941059 1 0)
  · exact layerOK2576941059k2
  · exact layerOK2576941059k3
def support2576941059 : List (Sig × Row × Row) := [(inputs.getD 0 zero,0,1),(inputs.getD 1 zero,0,2)]
theorem low2576941059 : Lower (vars 2576941059) (graphGoal 2576941059) 4 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g2576941059) (before_sound [] baseKnown) geom2576941059 checked2576941059 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 2576941059) (vars 2576941059) support2576941059=true := by decide +kernel
  apply essential_ok h a
  have e : support2576941059.map Prod.fst = vars 2576941059 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule15 : PlaneRule := ⟨[43690,52428],39321,4,liftPlane low2576941059 (by decide +kernel) (by decide +kernel),properPlane (p:=0) (n:=1) (by decide) (by decide)⟩
theorem geom3941335055 : graphValid g3941335055 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice3941335055k4p0 : mixedBlock g3941335055 4 0 5 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem slice3941335055k4p5 : mixedBlock g3941335055 4 5 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK3941335055k4 : mixedBlock g3941335055 4 0 6 := (@mixedJoin g3941335055 4 0 5 1 slice3941335055k4p0 slice3941335055k4p5)
theorem slice3941335055k5p0 : mixedBlock g3941335055 5 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK3941335055k5 : mixedBlock g3941335055 5 0 1 := slice3941335055k5p0
theorem checked3941335055 : mixedTables g3941335055 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g3941335055 0 0)
  · exact (mixedEmpty g3941335055 1 0)
  · exact (mixedEmpty g3941335055 2 0)
  · exact (mixedEmpty g3941335055 3 0)
  · exact layerOK3941335055k4
  · exact layerOK3941335055k5
def support3941335055 : List (Sig × Row × Row) := [(inputs.getD 0 zero,4,5),(inputs.getD 1 zero,0,2),(inputs.getD 2 zero,1,5),(inputs.getD 3 zero,1,9)]
theorem low3941335055 : Lower (vars 3941335055) (graphGoal 3941335055) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g3941335055) (before_sound [] baseKnown) geom3941335055 checked3941335055 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 3941335055) (vars 3941335055) support3941335055=true := by decide +kernel
  apply essential_ok h a
  have e : support3941335055.map Prod.fst = vars 3941335055 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule16 : PlaneRule := ⟨[43690,52428,61680,65280],60140,6,liftPlane low3941335055 (by decide +kernel) (by decide +kernel),properPlane (p:=2) (n:=0) (by decide) (by decide)⟩
theorem geom4009230351 : graphValid g4009230351 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice4009230351k3p0 : mixedBlock g4009230351 3 0 2 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK4009230351k3 : mixedBlock g4009230351 3 0 2 := slice4009230351k3p0
theorem slice4009230351k4p0 : mixedBlock g4009230351 4 0 5 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem slice4009230351k4p5 : mixedBlock g4009230351 4 5 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK4009230351k4 : mixedBlock g4009230351 4 0 6 := (@mixedJoin g4009230351 4 0 5 1 slice4009230351k4p0 slice4009230351k4p5)
theorem slice4009230351k5p0 : mixedBlock g4009230351 5 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK4009230351k5 : mixedBlock g4009230351 5 0 1 := slice4009230351k5p0
theorem checked4009230351 : mixedTables g4009230351 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g4009230351 0 0)
  · exact (mixedEmpty g4009230351 1 0)
  · exact (mixedEmpty g4009230351 2 0)
  · exact layerOK4009230351k3
  · exact layerOK4009230351k4
  · exact layerOK4009230351k5
def support4009230351 : List (Sig × Row × Row) := [(inputs.getD 0 zero,2,3),(inputs.getD 1 zero,1,3),(inputs.getD 2 zero,0,4),(inputs.getD 3 zero,1,9)]
theorem low4009230351 : Lower (vars 4009230351) (graphGoal 4009230351) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g4009230351) (before_sound [] baseKnown) geom4009230351 checked4009230351 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 4009230351) (vars 4009230351) support4009230351=true := by decide +kernel
  apply essential_ok h a
  have e : support4009230351.map Prod.fst = vars 4009230351 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule17 : PlaneRule := ⟨[43690,52428,61680,65280],61176,6,liftPlane low4009230351 (by decide +kernel) (by decide +kernel),properPlane (p:=3) (n:=0) (by decide) (by decide)⟩
theorem geom1717960707 : graphValid g1717960707 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice1717960707k2p0 : mixedBlock g1717960707 2 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=2) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK1717960707k2 : mixedBlock g1717960707 2 0 1 := slice1717960707k2p0
theorem checked1717960707 : mixedTables g1717960707 2 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g1717960707 0 0)
  · exact (mixedEmpty g1717960707 1 0)
  · exact layerOK1717960707k2
def support1717960707 : List (Sig × Row × Row) := [(inputs.getD 0 zero,0,1),(inputs.getD 1 zero,0,2)]
theorem low1717960707 : Lower (vars 1717960707) (graphGoal 1717960707) 3 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g1717960707) (before_sound [] baseKnown) geom1717960707 checked1717960707 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 1717960707) (vars 1717960707) support1717960707=true := by decide +kernel
  apply essential_ok h a
  have e : support1717960707.map Prod.fst = vars 1717960707 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule18 : PlaneRule := ⟨[43690,52428],26214,3,liftPlane low1717960707 (by decide +kernel) (by decide +kernel),properPlane (p:=1) (n:=0) (by decide) (by decide)⟩
theorem geom2901278735 : graphValid g2901278735 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,by decide +kernel⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
theorem slice2901278735k4p0 : mixedBlock g2901278735 4 0 5 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2901278735k4 : mixedBlock g2901278735 4 0 5 := slice2901278735k4p0
theorem slice2901278735k5p0 : mixedBlock g2901278735 5 0 1 := by
  apply mixedVerified
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem layerOK2901278735k5 : mixedBlock g2901278735 5 0 1 := slice2901278735k5p0
theorem checked2901278735 : mixedTables g2901278735 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g2901278735 0 0)
  · exact (mixedEmpty g2901278735 1 0)
  · exact (mixedEmpty g2901278735 2 0)
  · exact (mixedEmpty g2901278735 3 0)
  · exact layerOK2901278735k4
  · exact layerOK2901278735k5
def support2901278735 : List (Sig × Row × Row) := [(inputs.getD 0 zero,0,1),(inputs.getD 1 zero,0,2),(inputs.getD 2 zero,9,13),(inputs.getD 3 zero,1,9)]
theorem low2901278735 : Lower (vars 2901278735) (graphGoal 2901278735) 6 := by
  apply lower_impossible (proper_of _ (by decide +kernel)) _ (mixedRoot (g:=g2901278735) (before_sound [] baseKnown) geom2901278735 checked2901278735 (Nat.le_refl _) (i:=0) (by decide +kernel))
  intro a ha
  have h : checkEssential (graphGoal 2901278735) (vars 2901278735) support2901278735=true := by decide +kernel
  apply essential_ok h a
  have e : support2901278735.map Prod.fst = vars 2901278735 := by decide +kernel
  rw [e]
  exact List.mem_toFinset.mpr ha
def planeRule19 : PlaneRule := ⟨[43690,52428,61680,65280],44270,6,liftPlane low2901278735 (by decide +kernel) (by decide +kernel),properPlane (p:=1) (n:=0) (by decide) (by decide)⟩
def planeRules : Nat → PlaneRule
  | 0 => planeRule0
  | 1 => planeRule1
  | 2 => planeRule2
  | 3 => planeRule3
  | 4 => planeRule4
  | 5 => planeRule5
  | 6 => planeRule6
  | 7 => planeRule7
  | 8 => planeRule8
  | 9 => planeRule9
  | 10 => planeRule10
  | 11 => planeRule11
  | 12 => planeRule12
  | 13 => planeRule13
  | 14 => planeRule14
  | 15 => planeRule15
  | 16 => planeRule16
  | 17 => planeRule17
  | 18 => planeRule18
  | _ => planeRule19

end PEqualNP.Outside.L_meta_11008

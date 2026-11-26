import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_9822.Ranked
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
abbrev Row := Fin 1024
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

theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega
def onlyWire (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v
def kwWireB (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem kwWireB_sound {ws T v p n} (h : kwWireB ws T v p n=true) :
    onlyWire ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)
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
def rows (v i : Nat) : Row := Fin.ofNat 1024 ((v >>> (10*i)) % 1024)
def excluded (ws : List Sig) (T a b : Sig) (t : Nat) : Bool :=
  (a != b) && kwWireB ws T a (rows t 0) (rows t 2) && kwWireB ws T b (rows t 0) (rows t 3) &&
    kwWireB ws T a (rows t 4) (rows t 1) && kwWireB ws T b (rows t 5) (rows t 1)
theorem different {ws T a b t f} (ok : excluded ws T a b t=true)
    (law : orderLaw ws.toFinset T f) : f a ≠ f b := by
  simp only [excluded,Bool.and_eq_true,bne_iff_ne] at ok
  exact law.1 ok.1.1.1.1 (kwWireB_sound ok.1.1.1.2) (kwWireB_sound ok.1.1.2)
    (kwWireB_sound ok.1.2) (kwWireB_sound ok.2)
def child (bank : List Sig) (d : Nat) :=
  let a := bank.getD (d%32) zero
  let b := bank.getD ((d>>>5)%32) zero
  if d>>>10=4 then neg a else bin (d>>>10) a b
def liveList (m : Nat) : List Sig → List Sig
  | [] => []
  | a::as => if m%2=1 then a::liveList (m/2) as else liveList (m/2) as
abbrev Sample := Nat × List Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat
def state (raw : List Sig) (s : Sample) :=
  liveList s.2.2.1 (s.2.1.foldl (fun bank d => bank++[child bank d]) raw)
def replay (raw : List Sig) (T : Sig) (s : Sample) :=
  let (k,_,_,c,i,j,l,x,y,z) := s
  let ws := state raw s
  let a := ws.getD i zero
  let b := ws.getD j zero
  let d := ws.getD l zero
  ((ws.contains a && ws.contains b) && excluded ws T a b x) &&
    (if c=2 then decide (k+1≤ws.toFinset.card) else
      decide (k≤ws.toFinset.card) && ws.contains d && excluded ws T a d y && excluded ws T b d z)
theorem replay_sound {raw T s} (ok : replay raw T s=true) :
    ∀ k, k ≤ s.1 → ¬Live false T k (state raw s).toFinset := by
  obtain ⟨cap,ops,m,c,i,j,l,x,y,z⟩ := s
  let ws := state raw (cap,ops,m,c,i,j,l,x,y,z)
  let a := ws.getD i zero
  let b := ws.getD j zero
  let d := ws.getD l zero
  change (((ws.contains a && ws.contains b) && excluded ws T a b x) &&
    (if c=2 then decide (cap+1≤ws.toFinset.card) else
      decide (cap≤ws.toFinset.card) && ws.contains d && excluded ws T a d y && excluded ws T b d z))=true at ok
  intro k hk run
  change Live false T k ws.toFinset at run
  change k ≤ cap at hk
  obtain ⟨count,f,size,bounds,law⟩ := order_live run
  simp only [Bool.and_eq_true,List.contains_eq_mem,decide_eq_true_eq] at ok
  have ha := bounds a (List.mem_toFinset.mpr ok.1.1.1)
  have hb := bounds b (List.mem_toFinset.mpr ok.1.1.2)
  have ab := different ok.1.2 law
  by_cases hc : c=2
  · have small : cap+1 ≤ ws.toFinset.card := by simpa [hc] using ok.2
    omega
  · have more := ok.2
    simp only [hc,if_false,Bool.and_eq_true,List.contains_eq_mem,decide_eq_true_eq] at more
    have hd := bounds d (List.mem_toFinset.mpr more.1.1.2)
    have ad := different more.1.2 law
    have bd := different more.2 law
    obtain ⟨⟨⟨sc,_⟩,_⟩,_⟩ := more
    omega

def raw : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def target : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0ffffffffffffffffffffffffffffffffffffffffffffffffffffeaeaffffc0c0fffffffffffffffffffffffffffafff0ffffffffffffffffffffffffffeaffc0fffffffffffefcfcfffffffffffaf0f0ffeeeeeeffeeccccffeaeaeaffeac0c0
theorem shrink_only {S R : Finset Sig} {T a p n} (sub : S⊆R) (h : onlyWire R T a p n) :
    onlyWire S T a p n := ⟨h.1,h.2.1,fun v hv => h.2.2 v (sub hv)⟩
theorem common_difference {ws S T a b t f} (ok : excluded ws T a b t=true)
    (sub : S⊆ws.toFinset) (law : orderLaw S T f) : f a ≠ f b := by
  simp only [excluded,Bool.and_eq_true,bne_iff_ne] at ok
  exact law.1 ok.1.1.1.1 (shrink_only sub (kwWireB_sound ok.1.1.1.2))
    (shrink_only sub (kwWireB_sound ok.1.1.2)) (shrink_only sub (kwWireB_sound ok.1.2))
    (shrink_only sub (kwWireB_sound ok.2))
def makeWire (bank : Array Sig) (d : Nat) :=
  bank.push (bin (d%2) (bank[(d/2)%8192]?.getD zero) (bank[d/16384]?.getD zero))
def operations : List Nat := [16385,81927,114697,98315,114699,131083,147467,196619,114701,131085,147469,196621,131087,147471,147472,147473,180240,196624,196625,180242,196626,196627,196630,81929,98311,114695,131079,147463,540679,409607,98313,131081,147465,409609,409611,540685,409613,540686,409614,409615,540689,540691,409666,409667,655367,262151,131086,655374,262158,262159,655376,655377,262160,655379,262224,262225,671751,163852,65543,1097739,1097743,262226,1097761,262157,671758,32769,1228814,1245197,49153,65537,98309,1310723,1310734,262304,262305,131073,32770,1409039,1425489,655533,81923,1474574,98306,1507343,114691,655548,1540109,213180,131075,1605646,1605644,1638419,1654799,147459,1687566,655566,1720335,1687564,1277971,1753103,81925,1802252,1802259,1835090,1802254,1867795,1884173,1310731,360608,114692,1949709,147461,1982478,1998861,98307,114690,147458,655363,98308,147460,655364,655365,114700,147468,147470,655378,655362,2228239,688130,688132,688140,688142,688208,671746,262146,671748,262148,671756,262156,1425435,213165,1507345,2473999,1507347,2506767,2506796,2506797,1540101,262332,409788,1605651,2621506,213188,2654223,1753105,2686991,540674,409602,540676,409604,540684,409612,2228241,2818063,213006,213007,213008,213009,213010,131082,2932749,2949123,2949135,2949139,2932751,3014675,3014736,3014737,114698,147466,655370,294922,294928,294929,294930,294931,81922,360450,81924,98314,360458,360459,360460,360466,360528,360529,212994,3375119,3375123,3407887,212995,245762,212996,245764,245772,245774,294942,294943,1769508,245778,1802284,3604493,1540103,1540108,540860,131074,131076,131084,540688,540690,294978,81921,114689,671904,1982476,671986,49155,2506834,540832,1949713,3915783,196610,196613,196620,2179087,3997703,3997705,3997713,3997763,2179089,4079623,4079625,4079683,671762,294919,294994,327683,327684,327687,327694,327762,327763,98305,1867789,1409037,1688076,4341777,4358159,4358210,180226,4292612,180228,180236,4292622,180238,4292624,4292626,180748,197132,541196,410124,147457,4292615,4292617,4292619,950285,4292625,950289,4292627,672268,672269,262668,3801105,409760,1949715,4816909,1949707,4849677,1982928,4882443,4898829,4898898,196612,4947981,3801090,3801100,3801104,688144,180688,688592,688150,688152,606210,606211,606212,606217,606220,606222,606223,606224,606672,213456,213066,213067,3801091,3801097,3801099,606218,3801107,606673,294986,294987,3801101,360522,541136,410064,196618,229383,229457,294992,5095440,2195469,5586951,5586955,5586961,2195537,5652496,344074,344080,344082,672208,262608,98312,409608,409629,1507335,655922,671932,1638415,671950,671905,1949703,4849746,737283,737284,737285,737287,737294,737297,2228231,5832707,5832711,5832715,5832719,5832721,1835015,1835023,1392650,1458186,1392658,1458194,1458346,4325409,3211273,6275090,655530,1392647,1392649,1392651,1523723,1392659,1523719,1523721,1392654,737468,213162,655556,6488079,1392642,6520847,6537227,6537235,1835088,1802410,655580,671964,1802247,1802255,4816962,655599,6701066,6701074,6701226,262383,6766605,6766674,6701063,6701067,6701073,6701075,6176783,1998859,6897677,1392644,1392652,180394,655382,688138,606378,688298,655434,245834,245786,262314,1392643,311299,409610,540842,295082,376834,376844,377002,376898,376899,2244627,2146314,2146322,2146474,884740,884746,884750,884754,884906,671754,327690,327760,671824,2326538,2326542,2326698,3260431,7536659,7536720,212999,213072,3080199,7618572,7618578,7618640,3080201,7684108,7684114,3080205,7733251,7733255,7733265,7733266,7733267,3080209,7831559,7831561,7831571,7831633,3080273,7913490,229378,229388,229394,229546,229456,245767,3096585,8044546,8044548,8044558,3096589,8110083,8110087,8110095,8110097,3096593,8192007,8192009,8192015,8192081,6176775,8273922,8273924,8273932,8273934,8273938,8274000,6176777,8388610,8388612,8388620,8388622,8388626,6176781,8486915,8486916,8486919,8486926,8486927,8486930,8486931,6881299,6881360,6881361,6881287,6176787,8683522,8683524,8683527,8683532,8683534,8683600,8683601,6176849,8814596,8814606,8814610,737298,737450,2179079,2179083,8929287,8929289,8929294,8929295,8929450,8929360,3997867,3997776,409680,6946831,9093131,9093139,360455,2195463,9158666,9158826,9158736,5095434,5095594,5586947,2195473,9273351,9273353,9273354,9273355,9273424,9273425,5652490,5652650,376842,376912,376913,933895,933897,933899,933905,933907,344234,999428,999434,999438,999442,2211847,9633794,9633796,9633802,9633806,9633962,2211851,9732098,9732100,9732103,9732109,9732110,9732111,9732113,9732266,2211855,9879565,9879569,9879723,9879559,2211857,9961474,9961476,9961479,9961482,9961485,9961486,1032196,1032202,1032206,1032362,6307855,10141707,10141715,3080211,10190855,10190857,10190931,262145,1835020,6881282,6881292,6881362,6881363,6881312,2195467,10371079,10371081,10371155,7913475,7913479,7913491,65538,65540,114696,147464,294920,8814595,8814597,8814599,2801673,10616842,10616846,1475122,671924,1507339,10698759,7585808,1802802,541234,4784288,4849671,4603916,10813455,10829841,4603906,4603908,4603918,4603920,295474,10829831,10829833,10829835,10829843,10829891,5833049,672306,213554,213074,4603912,294944,294945,4603914,361010,360530,7585795,7585796,7585797,7585806,7585807,7585809,7586354,245768,246322,65539,11337740,11354127,1474572,11386895,1507329,540673,409785,11452482,11452453,1523713,1523779,262329,1523745,1523795,10698834,2473991,10698753,410906,1572930,409792,2048017,11681793,11681799,11681801,11681803,11681805,11681858,11681859,409851,11812865,11812871,11812873,11812875,11812877,11812930,11812931,2048013,11943947,11943955,11943969,11681824,409690,6389826,3735571,12058812,3751953,12091580,3653643,3653665,10534913,10534919,5783563,12189884,7143433,12222652,540868,1605639,262340,1720337,12304399,12304450,540878,1687553,295118,12386321,12402754,12386370,1785857,1785863,1785865,1785867,1785922,1785923,770065,12550350,3735567,12583118,11436034,11436036,11436044,11436046,410996,2719759,12697611,12697613,12697617,12697619,411151,540677,12795918,12812301,606274,360514,360515,622594,622596,622604,622606,409676,327746,409640,409624,213058,671810,262210,950273,950279,950355,851969,851970,851972,851975,851980,851981,851982,851983,409682,852050,409632,852000,852001,1163265,1163266,1163268,1163271,1163276,1163277,1163278,1163279,1163281,1163283,1163330,294996,2293775,13533185,13533191,13533195,13533201,13533203,13533250,409626,409627,409636,13647873,13647874,13647876,13647879,13647881,13647886,13647887,13647889,13647891,13647938,13647939,2621447,2621453,360480,360484,410758,2162689,2162695,2162707,13991937,13991943,13991945,13991947,13991953,13992003,2162755,294914,14123027,14139458,294916,14172161,14172167,378563,2179073,2326564,4079627,376836,14286849,14286855,409605,14336066,3751943,14368770,14368772,14368784,14368804,3178497,14450690,14450692,14450704,14450754,3178505,14532610,14532612,14532624,3178513,14598153,14598155,14598210,14598211,14598145,14598151,311303,2621454,2785295,14745617,14745619,411400,411401,2785281,2785287,2785289,409941,12025857,12025858,12025860,12025863,12025867,12025870,12025871,12025873,12025875,2621441,2621484,770049,770055,770061,12550145,12550151,12550155,12550156,12550157,12550163,12550194,278530,278540,409634,6389762,6389764,6389772,6389774,12042242,12042244,12042247,12042249,12042251,12042252,12042253,12042254,12042255,12042257,12042259,2736143,15532043,15532045,15532049,15532051,2621452,15613967,14336014,15646733,573490,638978,638980,638988,638990,639042,704514,704516,704524,704526,720897,720898,720900,720903,720908,720910,15925261,2801665,15958030,15958082,2801671,16007182,16007234,16007218,2801675,16072705,16072711,16072718,16072719,16072723,16072770,2801679,16187401,16187411,16187458,16187459,16187393,16187399,13860878,753665,753668,753671,753678,753730,753731,786433,786439,786441,16449548,786445,786499,802817,802818,802823,802825,802828,802882,802883,819202,819204,819212,819214,835586,835588,835596,835598,16744461,16744465,851971,16793650,868354,868356,868364,868366,9273345,16891914,16891984,9961473,16941058,16941060,16941066,16941070,16941136,606216,311304,311328,1949697,950281,17104908,13107212,17104928,13107232,4702209,13107201,4702215,13107207,4702220,4702221,13107213,14532619,17301506,17301508,17301520,17301540,3178507,180264]
def lookup : List Nat := [1,2,0,3,4,5,6,7,8,9,10,236,640,196,124,125,225,126,641,198,128,226,129,68,11,34,35,36,37,33,352,40,642,12,41,643,42,199,13,188,14,179,15,189,16,132,18,227,19,133,20,67,56,22,134,23,324,76,24,25,434,755,78,79,231,262,270,282,283,284,273,332,275,286,276,288,697,232,85,281,127,210,91,406,387,143,145,66,453,50,111,117,147,61,407,74,28,253,43,405,234,235,269,271,325,241,242,38,336,17,272,463,243,21,274,337,26,490,27,29,55,30,31,32,698,166,168,170,45,47,390,167,169,39,353,436,44,171,46,48,49,228,229,51,918,52,53,130,131,54,626,144,146,190,148,73,57,58,59,60,62,135,63,64,65,69,70,71,72,96,254,644,191,175,192,193,194,195,304,326,305,306,292,328,1043,313,256,104,754,77,485,486,201,487,354,749,89,150,99,386,108,435,898,258,748,157,222,223,224,329,81,82,83,84,361,659,297,120,295,375,290,308,1008,683,684,685,366,686,687,655,688,323,212,174,176,177,178,321,149,382,355,93,708,152,154,702,399,347,338,348,205,349,577,88,218,137,95,97,658,409,422,123,303,138,139,427,140,141,307,309,310,211,213,690,214,215,219,315,197,558,200,202,203,559,311,633,341,566,377,388,424,393,379,403,423,398,425,385,363,654,389,395,518,358,102,1041,847,954,848,899,106,109,165,263,575,116,627,376,113,488,420,118,240,426,369,173,448,449,450,451,452,429,142,433,967,432,555,713,383,696,709,464,391,392,155,156,714,729,715,716,717,718,721,158,204,180,159,207,209,952,161,163,257,454,259,455,787,788,789,790,796,181,182,183,184,185,186,187,811,339,371,907,460,461,473,465,466,474,479,467,623,469,470,483,480,471,624,472,475,476,477,478,481,622,216,217,496,491,495,500,501,502,499,503,798,799,1044,285,287,852,855,853,856,579,861,858,854,456,986,850,990,793,869,660,544,546,316,245,250,457,547,458,246,251,545,548,549,871,244,440,247,249,665,1031,565,560,634,342,317,567,563,635,345,340,568,343,570,569,344,666,505,221,663,664,677,680,742,657,312,314,1040,327,318,319,233,360,230,770,771,772,773,334,350,238,365,437,237,248,252,255,260,261,289,652,291,279,280,996,357,267,268,277,278,820,800,356,370,372,373,374,675,667,656,681,320,335,378,380,322,330,331,887,760,351,293,416,410,417,418,411,419,300,301,333,1010,489,573,617,346,572,603,439,552,974,977,648,981,988,993,994,989,985,1012,651,674,1034,367,368,542,543,364,394,359,408,362,414,415,691,428,946,673,444,809,404,381,776,384,438,538,706,722,933,935,936,735,583,1039,676,934,998,584,585,586,587,397,752,762,763,400,401,402,512,628,529,629,523,526,630,631,530,441,682,412,431,970,533,430,442,443,795,831,445,446,447,619,459,462,637,468,638,482,484,639,492,493,494,497,498,504,1049,519,645,646,506,507,508,521,509,510,511,647,513,514,515,516,517,520,522,524,525,527,528,531,532,534,535,536,537,539,540,541,550,551,553,554,556,557,561,562,564,571,574,576,578,580,581,582,588,589,590,591,597,592,607,611,593,594,595,596,598,599,600,601,602,604,605,606,608,609,610,612,613,614,615,616,618,620,621,925,625,632,636,743,797,857,1032,649,846,965,650,689,678,679,661,668,670,662,671,669,672,1061,750,785,786,849,835,701,957,833,834,1042,694,784,730,700,705,707,710,805,703,711,712,719,720,1009,723,724,725,726,727,728,731,732,733,791,794,1011,734,1001,930,931,932,1014,802,804,746,744,806,807,808,738,736,774,801,810,812,813,792,909,910,912,840,913,914,915,916,917,919,937,939,940,941,942,943,944,945,947,961,962,960,1013,958,963,966,968,971,972,999,1000,1015,1017,1018,1019,1021,1022,1027,1029,1030,768,877,878,880,775,803,1056,879,881,882,888,889,890,892,825,891,911,938,959,948,964,969,997,1016,1020,1028,737,739,740,741,1054,1055,893,895,1057,1058,1059,1060,1062,745,747,951,753,758,759,761,764,765,920,921,922,766,923,924,926,927,928,767,769,777,778,779,780,1026,783,1047,814,815,816,817,818,819,821,822,823,824,826,827,828,829,830,832,836,837,838,839,841,842,843,844,845,851,859,860,864,866,867,868,870,873,874,876,883,884,885,896,886,897,894,905,906,900,901,902,903,904,908,929,949,950,980,956,973,1007,982,975,976,983,978,979,984,987,991,992,995,1002,1003,1004,1005,1006,1023,1024,1033,1035,1036,1037,1038,1048,1051,1045,1050,1052,1046,1053]
def frame := let bank := operations.foldl makeWire raw.toArray; lookup.map (fun j => bank[j]?.getD zero)
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem frameSize : frame.length=1002 := by decide +kernel
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem frameUnique : frame.Nodup := by decide +kernel
abbrev Port := Fin 1002
def port (i : Port) := frame[i.val]'(by rw [frameSize]; exact i.isLt)
theorem port_mem (i : Port) : port i ∈ frame := by
  unfold port
  exact List.getElem_mem _
theorem port_inj : Function.Injective port := by
  intro i j h
  apply Fin.ext
  exact (List.Nodup.getElem_inj_iff frameUnique (hi:=by rw [frameSize]; exact i.isLt)
    (hj:=by rw [frameSize]; exact j.isLt)).mp h
set_option maxRecDepth 64000 in
set_option maxHeartbeats 0 in
theorem frameRule : excluded frame target (port 0) (port 1) 148691409238696966 = true := by decide +kernel
def addressTail : Nat → Nat → List Port
  | 0,_ => []
  | n+1,r => Fin.ofNat 1002 (r%1024) :: addressTail n (r/1024)
def addresses (code : Nat) : List Port := 0::1::addressTail (code%16) (code/16)
def fromAddresses (code : Nat) := (addresses code).toFinset.image port
def codeOK (code : Nat) := decide (addresses code).Nodup
theorem length_tail (n x : Nat) : (addressTail n x).length=n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [addressTail,ih]
theorem closedCode {code : Nat} (ok : codeOK code=true) : ∀ q, q≤code%16+1 →
    ¬Live false target q (fromAddresses code) := by
  intro q hq run
  have nd : (addresses code).Nodup := of_decide_eq_true ok
  have size : (fromAddresses code).card = code%16+2 := by
    rw [fromAddresses,Finset.card_image_of_injective _ port_inj,List.toFinset_card_of_nodup nd]
    simp [addresses,length_tail]
  have sub : fromAddresses code ⊆ frame.toFinset := by
    intro w hw
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hw
    exact List.mem_toFinset.mpr (port_mem i)
  have ha : port 0∈fromAddresses code := Finset.mem_image_of_mem _ (by simp [addresses])
  have hb : port 1∈fromAddresses code := Finset.mem_image_of_mem _ (by simp [addresses])
  obtain ⟨count,f,mass,limit,law⟩ := order_live run
  have aa := limit _ ha
  have bb := limit _ hb
  have different := common_difference frameRule sub law
  omega

def addFields : Nat → Nat → List Nat × Nat
  | 0,v => ([],v)
  | n+1,v =>
    let (tail,z) := addFields n (v/1024)
    (v%1024::tail,z)
def packFields : List Nat → Nat
  | [] => 0
  | x::xs => x+1024*packFields xs
def decodeCluster : Nat → List Nat → Nat → List Nat
  | 0,_,_ => []
  | n+1,prev,v =>
    let (tail,z) := addFields ((v/16)%16) (v/256)
    let fields := (prev.take (v%16))++tail
    (fields.length+16*packFields fields)::decodeCluster n fields z
def cluster0 := decodeCluster 192 [] 0x2886ca11b2546c711b1744e2a1383b2a138372a1386c3e0d4a84e090a84e088a84e0841f391383b2a138352a138302a1381f070e44e09019035204f1b1382e0a8e42e0a81c031224c1a7386989138a6520eca5dd0b8a6f81bbdc6d311b3ac6caf1b2746c961b2286c5d1b1346c491b1006c370c02c3913c6c4e0b82a391343b0a0e6151a13c3b2a13c352a1386c400c8a84f1b1002e2a13c26088e4300b021398e46871134a84e0b0a84d0a01f39c4c6af61a1343b2a138372a2c06c8e1b1c46c4f1b1386c370b8a82e090a82e088a83b1b0b8210740b4829c6c9e1b2746c9b1b2486c8f1b2206c781b1886c601b17c6c5d1b1646c571b0ec6c371b0d46c321b0c06c2e0b0a82c0a8a82c0a0a82c098a82c09022390b022084e4a41b28c6ca21b2806c9f1b2786c9d1b2706c951b23c6c881b2006c781b1c46c5d1b0ec6c371b0d46c340b0a82c0a8a82c0a0a82c090a82c088a82c0841f39c4c6af61a2486c911b23c6c8c1b22c6c8a1b2206c851b2046c801b1b46c6b1b1886c590eca83b0dca83b0d4a83b0c8a83b0c0a8b01b2386c711b0ec6c370b8a83b0b0a83b0a8a83b0a0a83b098a83b1b0b8242a0ec6c2e1b0b0222a0ec6c2e084a83b1b0b01f074e42e0a8a82c088a82c07ca83b1b0d41d070e42c088a82c07ca83b1b0dc1d06ce42c088a82c07ca83b0741a390b0222a0ec1d064e42c088a87b1b1e86c791b1dc6c761b1d06c711b1b46c601b0ec6c3a1b0dc6c351b0c86c301b0b86c2c1b0a86c281b098212a0b01f2a0ec1d0600a0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster0_ok : cluster0.all codeOK = true := by decide +kernel
def cluster1 := decodeCluster 192 [] 0xec352a0ec322a0ec302a1c46c4f1b1386c3f1b0ec2e2a0ec2c2a0ec2a2a0ec262a0ec6c2e090a83b1b0b86c2c088a83b084a84e1b0ec1f074e44e0eca84e0d4a84e0c0a84e0b0a84f1b1386c4d098a84e07c1c3907c1d06ce43f0b0a84d090a832088a841084a84e07c18391383b05c0f4893069ce1a6244e299483b293204f0d4e5dd0b8a44f1b1386c3e0b82a391343b0a0e46f13c2639854684f0eca84f0d4a84e1b100322a13c6c400b8a8a71b2786c9d1b26c6c961b2486c8f1b2206c781b1886c601b17c6c5d1b1646c571b1506c4f1b1386c4d1b1046c401b0fc6c3b1b0dc6c351b0c86c301b0b82c2a0b02a2a0b0282a13c6c2c098a82c09022391006c2c08821398e469281a4a46d241b48c6d201b2886ca11b2706c991b2546c801b1c46c5d138a871134a84e0eca84e0dca84e0d8a84e1b0f8352a1382c2a1382b2a1382a2a0f8292a1386c4d0a0a84e09ca84e090a84e1b0b0222a1386c4d0841f39c4c6af61a2486c911b23c6c8c1b22c6c8a1b2206c851b2086c811b2006c7c1b1b46c6b1b1886c591b13c6c4e1b1346c411b1006c3f1b0f83b2a1386c3b0dca83b0d4a83b0c8a83b0c0a8b01b2386c711b13c6c4e1b0fc6c3b1b0dc2e2a0ec2c2a0ec2a2a0ec282a0ec262a0ec6c2e090a83b1b0b86c2c088a83b1b0b8212a1386c3b07c1d391383b2a1386c4d0d4a84e0c0a84d0b8a84e0b0a84f1b1386c4d098a84e07c1c390dc1d06ce42c0881a390fc2c2a134242a1346c411b100212a1381f0600e4813c3b2a13c352a138322a13c2e0880d0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster1_ok : cluster1.all codeOK = true := by decide +kernel
def cluster2 := decodeCluster 192 [] 0x3131abd8684f1b1386c4d1b1046c401b0fc6c3e0eca84e0dca8711b13c6c4e1b0fc6c3b0b8a82e090a84e07c1d391383b2a138352a1382c2a0b82a2a1386c4d098a84e07ca8350741c390dc1d06ce43b0741a390fc2c2a134242a1046c40084a84e07c18051204f0eca84f0d4a84e0c8a84f0b822392886ca11b2546c711b1744e2a1383b2a138372a1386c3e0d4a84e090a84e088a84e0841f391383b2a138352a138302a1381f070134813c6c4e0b82a049224c138a44e1b0f82e0a8e4400b8223910022084e6391a4a069291b4806c991b2546c801b1c46c5d138a84e1b0f8352a1382a2a0f8292a138282a138222a1382107ce4711b1386c3f0b8a82e088a84e07c1d390b81d06ce4411b100212a1381f06011487742e291bc4f098e4b01b2386c711b13c6c3f0b8a82e0901d3913c6c4d0981c390fc2c2a134242a1046c4008418041224c138a6520eca4c813c35397742e2913c6c4e1b0f82e0a8e46f13c263913c3b2a13c352a1386c400c8a84f1b1002e2a29c6c9e1b26c6c961b2486c8f1b2206c781b1886c601b1746c591b15c6c541b13c6c4e1b1346c411b1006c3f1b0ec6c351b0c86c301b0b82c2a0b02a2a13c6c2c098a82c09022391006c2c08821398e469281a4a46d241b4806ca21b2846c991b2546c801b1c46c5d138a84e0eca84e0dca84e1b0f8352a1382c2a1382b2a1382a2a0f8292a138282a138242a1386c2c088a84e0841f39c4c6af61a2486c911b23c6c8c1b2286c881b2146c821b2006c7c1b1b46c6b1b1886c591b13c6c4e1b1346c411b1006c3f1b0f83b2a138370740f0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster2_ok : cluster2.all codeOK = true := by decide +kernel
def cluster3 := decodeCluster 192 [] 0x4d1b1046c400d4a8410d0a84d1b1046c400c8a84d1b1046c400c4a84d1b1046c400c0a84d1b1046c400bca84d1b1046c400b8a8410b4a84d1b1042c2a1346c410a8a8410a0a84d1b10426084e6391a4b469431b4a46d281b49c6d261b4906d231b4886ca21b2846c9c1b2506c931b2006c771b1c86c711b1b86c671b1986c5d1b1404e2a1c44d2a1383b2a138372a1386c4d0d8a84e0d4a84e0c8a84e0c4a84e0c0a84e1b1342e2a1382d2a1382c2a1382a2a1386c4d0a0a84e098a8a11b2706c761b0ec6c3a1b0c46c2f1b0a02107ce79c1ac4c6ae71a8b469601a1886c4f1b1386c4d1b1043b2a1386c3b0dca8b01b2386c711b13c6c4e1b0c42e2a0b8242a0b81f074184822c4e0ece44f1b1382e0a8e44d0ec28391383b098e44e0ec25390b82c088e6f61a8b469601a4dc683b0dca8b01b2386c371b0c42e07417489304e291386c3e0b82a391002e088e44008821398e469281a4a46d201b2646c951b2006c711b1744e2a1386c3e0d4a84e0a8a83e0a4a84e0a0a84e088a84e0841f391c46c4e1b0fc2e2a0b8222a1381f074e42e0741b391046c40084a84e07c1805921dd0b8a46f13c26392c06c8e1b1c46c4f1b0fc2e2a0b824074e44f1b13426070e43f0b0a84d090a8411b100212a0841f06015489304e299483b293204f0d4e5dd0b8a44f0b82a391bc4f098e6151a13c3b2a13c352a100322a13c6c400b8a84f1b1386c4d1b1046c401b0fc2c2a13c26088e44008821398e469281a4a46d201b2886c991b2546c801b1c44e2a138372a0f8352a1382c2a138282a138242a1382107c140240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster3_ok : cluster3.all codeOK = true := by decide +kernel
def cluster4 := decodeCluster 192 [] 0x3131abd86ae71a58069371abd46c8c1b1f46c7c1b1046c400eca84e0dca83b0d4a8b01b2386c711b13c6c4e1b0dc6c310b8a82e090a82e084a82e07c1d069224c1a7386989138a5ce134a6e11a9483b297742e291382e0a8e44d0ec28394804e2a138302a13827090e6151a13c3b2a1386c400c8a8400b8a84f1b1386c411b1002c088e6391a4b46871134a84d0d8a84d0b8a84d0a01f39c4c6af61a580684d1b1046c400eca84e0dca8b01b2386c711b1386c370b8a82e090a83b084a82e07c1d065222b1a73869031a3104e2973868da1a31468c4134a6e11a9483b297742e292806c9e1b2746c9b1b2686c981b25c6c880fca83f0eca83f0dca83f0d4a83f0d0a83f0c8a83f0c0a83f0bca83f0b8a83f0b42c391382e0a8e44d0ec28394386d0d1b4306d0b1b4286d081b41c6cdd1b2d46cb41b2c86ca21b23c6c7a1b1d06c721b1b86c671b1986c62134a84d0eca84d0dca84d0d4a84d0d0a84d0c8a84d0c0a84d0bca84d0b8a84d0b4a84d0b0a84d0a8a84d0a0a84d09824398546b761b5a86c9b1b19c6c561b13c6c400c8a84f1b1002e2a1346c410b0a83209822391ec6c7a1b1e46c771b1d86c741b1c46c701b1b86c6d1b1804d2a8006dff1b1ec6c7a1b1e46c771b1d86c741b1c86c711b1c06c6e1b1b46c6a1b1a46c671b1986c601b1286c481b1186c42104a87a1b1e46c761b1c46c701b1a86c691b180402a1346c411b1003b2a1346c411b1003a2a1346c411b100372a10436084180240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster4_ok : cluster4.all codeOK = true := by decide +kernel
def cluster5 := decodeCluster 192 [] 0xb82a2a13c6c4e1b13426088e44e0eca84e1b134352a138302a1342e2a1382c2a13c6c4e1b13426084e42e0a820398e4692d1a9c86e421b7846ddf1b7786dca1b6d06d291b49c6d261b48c6d221b4806ca21b2706c991b2506c931b2006c711b1746c50138a871134a84e0eca84e0dca84e1b134352a138322a138302a1386c4d0b8a84e0b4a84e0b0a84e0a8a84e1b134282a138272a13c6c4e1b134262a1382507ce79c1ac4c6af61ab9c6a2d1a58069371a2486c881b2106c591b1386c4d1b1046c400eca84e0dcaafa1bbc46ef01b87c6dde1b4586cc01b2d86caf1b2306c7d1b1f06c601b13c6c4e1b1346c411b100352a1386c350c0a84f1b1386c4d1b0ec2e2a0ec2d2a1382c2a0ec2a2a0ec282a13c6c4e1b134260741c4873869891a40c68c4138a5ce134a6e11a9483b2977469540b8a44f0b82a391343b0a0e6151a100322a13c6c400b8a8411b0b82c2a13c26088e471134a84d0d8a84d0b8a84e1b1342807ce79c1ac4c6af61ab9c6a2d1a58068411b1003b2a89c6c8c1b1f46c7c1b100372a0dc352a0dc322a3e06cb11b2c06caf1b2b46ca91b23c6c8e1b1c46c591b1386c470b8a82e0b4a83b1b0b82c2a0b82a2a0dc262a0b8242a1fc6c361b0981f0741b489306a2b1a73869891a40c68c4138a6e11a9483b297742e2913c6c4e0b82a391343b0a0e44f0eca84f0d4a84e1b100322a13c6c400b8a8400b0a84f09822398e4692d1a4804e2a1c44d2a138372a1342e2a1382c2a1342807ce79c0741a0240801c060140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster5_ok : cluster5.all codeOK = true := by decide +kernel
def cluster6 := decodeCluster 192 [] 0x4e0f0a84e0dca84d0d4a84e0c830393306a121b8446de31b7886de11b6d06d151b3446ccb1b2e46cb71b2d86cb31b2c46caf1b2b86cad1b2b06ca91b2146c781b1c46c68134a84e1b1343b2a134382a1386c4d0d4a84d0c8a84e1b134302a1342f0b8e44e0eca84e0d42d395346d271b4986d231b4886c9e1b2746c9b1b2686c981b25c6c8f1b2204e2a1386c4d0d4a84e0c0a84e1b1342e2a1382d0b0e44d0d4a9e01b7786dca1b6546d941b3006caf1b13c6c4e1b1346c3f1b0d42e2a1382c0a8e44d0b829391386c4d0eca84e1b134352a138302a1342e2a1382c0a0e44e0eca84e0d4a84e0c027397886d151b3ac6cea1b3a46ce81b39c6ccb1b2e46cad1b2146c801b1e06c5b1b1444f2a9086e101b77c6dde1b7286db41b4b46d271b4986d231b4886ceb1b3a46ce81b2b46c9b1b2006c5b1b1444e2a8406e0c1b78c6de21b77c6dde1b7286db41b4546ced1b3ac6cea1b3a46ce81b39c6ccb1b2e46cb51b2d06cb21b2b46c9b1b2146c801b1e06c5b1b1444d2a1386c4d0eca84e1b134372a13c6c4e1b134352a13c6c4d0d0a84e1b134322a13c6c4e1b134302a1342f2a13c6c4e1b1342e2a1386c4d0b4a84e1b1342c2a13c6c4e1b1342a2a13c6c4e1b13428098e44e0eca84e1b134352a1342e094e44e1b134352a138302a1342e2a1386c4d0982439854684d0d4a84e1b100322a1346c400b8a84e1b1346c411b1002c0881c0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster6_ok : cluster6.all codeOK = true := by decide +kernel
def cluster7 := decodeCluster 192 [] 0xaf1b2b86cad1b2a86ca91b2386c8d1b1fc6c791b1d86c701b13c6c4e1b1346c471b1046c401b0ec6c3a1b0dc6c351b0c86c311b0c06c2f0b8a83b0b4a83b1b0b82c2a0ec6c2e0a8a83b0a0a83b1b0b826084e6f61a58069451a4b468f31a2846c9c1b24c6c8e1b2046c7f1b1f86c7d138aaac1b2706c931b2446c8c1b22c6c8a1b2246c881b2146c841b20c6c821b2046c7f1b1f86c7d1b13c6c4e1b1346c411b1003b2a1386c3b0dca84e1b134362a1386c3b0d4a84e1b0ec322a138312a1386c3b0c0a9e61b2c46cb01b2bc6cae1b2b46caa1b2846c9f1b2706c8e1b2346c811b13c6c4e1b1346c471b1046c401b0ec6c3a1b0dc6c361b0d46c341b0c86c300b8a84e1b0ec2d2a1386c3b1b0b82c2a1386c3b1b0b82a2a1386c4d1b0ec6c2e0a0a84e1b0ec6c2e0981f07520d92d8a4b62a4a4b6190a4f313ca64c1a8ac69891a4e469371a4bc69051a40c68f31a31468c4138a4d8134a6e11a94869211b2d86c8c1b22c6c8a1b2246c881b21c6c841b20c6c621b1504e2a138492a1383c0ece5211b4646d181b4586cc01b2bc6c8c1b2086c601b1504e2a87c6de11b6d06d191b4606cc01b2dc6cb31b2bc6c8c1b1a06c60134a84e124a84d11ca84e0f0a84d0eca84d0e0a84e0dc35391386c4d0d432394846ceb1b3246cb61b2bc6c8a1b2086c5d1b1504e0c01c0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster7_ok : cluster7.all codeOK = true := by decide +kernel
def cluster8 := decodeCluster 192 [] 0x4e1b0ec372a0ec352a0ec322a0ec302a2c06c8e1b1c46c4f1b1386c3f1b0ec6c370b8a83b0b42639bd86ae71a8b469601a4dc690b1b4286d081b41c6c911b2306c8b1b2286c891b2206c851b2106c831b2086c811b1fc6c7e1b1f46c4e1b1346c411b1003b2a138372a0ec352a0ec302ad786de61b4306d0b1b4286d081b41c6cb11b2bc6cae1b2b46caa1b2a46c8d1b2046c7f1b1f86c7d1b13c6c4e1b1346c471b1046c401b0ec6c371b0d46c341b0c86c301b0bc2e2a0ec6c2e0b4a82e0b0a83b1b0b82a2a0ec6c2e0a0a83b1b0b826090e6f61ab9c6a2d1a85469681a58069371a4bc687e1b1f46c4f1b1346c411b1003b2a138372a13c352a1386c400c8a9e61b2c46cb01b2bc6cad1b2a86ca91b2386c811b1fc6c7d1b1846c5c1b1546c4f1b1386c4d1b11c6c411b1006c361b0c86c310b8a82e0b4a8a71b2786c9d1b26c6c9a1b2606c971b2586c881b2046c7f1b1f86c7d1b1e06c5f1b1706c4f1b1386c4d1b1046c3b1b0dc6c351b0c86c301b0b86c2d0b0a82e0a8a82e0a0a84f1b0b826088e6f61ab9c6a2d1a58069371ac446c911b2306c8b1b2286c891b2206c851b2106c831b2086c811b1fc6c7e1b1f46c701b1a46c4f1b1386c4d1b1046c400eca84e1b0ec372a0ec352a0ec322a0ec302a7986cb11b2c02e0841d0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster8_ok : cluster8.all codeOK = true := by decide +kernel
def cluster9 := decodeCluster 192 [] 0x3b0d4a8711b13c6c4e1b0fc6c3b0b82d39e706b131ab9c6a2d1a58069371a2786c9d1b26c6c9a1b2606c971b2586c921b2446c8c1b22c6c8a1b2246c851b2106c831b2086c811b2006c7f1b1f86c7d1b1f06c781b1b46c6b1b1886c591b1386c4d1b1046c3f1b0f83b2a138372a0ec352a0ec302a1c46c4f1b1386c3f1b0ec6c370b8a83b0b42c39e706b131ab9c6a2d1a58069371a2486c911b23c6c8c1b22c6c8a1b2246c851b2106c831b2086c811b2006c7f1b1f86c7d1b1f06c6d1b1ac6c621b13c6c4d1b1046c3f1b0f83b2a1386c3b0dca83b0c8a8b01b2386c711b13c6c4e1b0fc6c3e1b0ec6c371b0c42e2a0ec2d0a8e79c1ac4c6ae71a8b469371a3086cc01b2cc6cad1b2786c921b2446c8f1b2306c8a1b2246c851b2106c831b2086c801b1fc6c7e1b1f46c7c1b1cc6c6d1b1ac6c621b1786c591b13c6c4e1b1346c411b0fc6c3e0eca84e1b0ec372a0ec352a0ec322a0ec302a2c06c8e1b1c46c4f1b1386c3f1b0ec6c310b82839c4c69601a1bc4f2abdc6ef61b9d46ceb1b3a46ce81b2b46c9b1b2486c911b23c6c8c1b22c6c8a1b2246c851b2106c831b2086c811b2006c7f1b1f86c7d1b1f06c6f1b1b46c6b1b1886c5b1b1646c511b13c6c4e1b1346c451b1046c3f1b0f83b0981d0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster9_ok : cluster9.all codeOK = true := by decide +kernel
def cluster10 := decodeCluster 192 [] 0xa91b23c6c8e1b2046c801b1fc6c7e1b1f46c711b1b46c6b1b1644e2a2c06c8e1b1c44d2a2c06c8e1b1c4472a2c06c8e1b1c4412a2c06c8e1b1c4402a7986cb11b2c06caf1b2b86cad1b2a46c8e1b2346c811b1fc6c7e1b1f43f2a2c06c8e0f8aaf41bbcc6de61b3e06cb11b2bc6cad1b2a86ca91b2486c911b23c6c8c1b22c6c8a1b2246c881b2146c841b20c6c821b2046c801b1fc6c7e1b1f46c7c1b1c46c6d1b1ac6c621b1646c4f1b1386c4d1b11c6c411b1006c3f1b0f86c3b1a1c46c3f0e8aa741b7986de21b3e06cb71b2c46caf1b2b86cad1b2a86ca91b2786c8f1b2346c8c1b2006c7f1b1f06c7a1b1c46c6d1b1ac6c591b13c6c4e1b1346c471b1046c401b0fc6c3e1b0ec372a1c46c4e1b0fc362a2c06c8e1b1c46c4f1b1386c3f1b0ec6c370d4a8711b13c6c3f0d0a8711b13c6c4e1b0fc6c3b1b0dc322a7986cf81b2bc6cad1b2a86c7c1b1c46c6d1b1ac6c591b1386c4d1b11c6c401b0fc6c3e1b0d4312a2c06c8e1b1c46c4f1b1386c3f1b0ec6c370c0a8711b13c6c3f1b0dc2f0b8e7131abd86bac1b6a06da71b6946da31b2486c911b23c6c8c1b2286c881b2146c821b2006c7c1b1b46c6b1b1886c591b13c6c4e1b1346c411b1006c3f1b0f83b2a138370b41d0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster10_ok : cluster10.all codeOK = true := by decide +kernel
def cluster11 := decodeCluster 192 [] 0x841b20c6c821b2046c801b1fc6c7e1b1f46c7c1b1b46c6b1b1886c601b13c6c4d1b1046c401b0fc6c3e0eca84e1b0ec370d4e7131abd869601a32c6cba1b2c46ca41b2886c9b1b2486c911b2306c8b1b2286c881b2146c841b20c6c821b2046c801b1f86c7d1b1f06c6d1b1ac6c621b1646c4e1b1346c4b1b1046c401b0fc6c3e0eca84e0dca83b0d43239c4c6af61a5806a371b3ac6cca1b3246caf1b2486c911b23c6c8c1b22c6c8a1b2206c851b2106c831b2086c811b2006c7e1b1f46c7c1b1b46c6b1b1886c5d1b13c6c4d1b1246c411b1006c3f1b0f83b2a1386c3b0dca83b0c83039eb86b7c1adc06b131abd86af31a75069c21a6fc69601a7986cf82c0a8b02bca8b02b8a8b02b4a8b02a8a8b02a4a9e61b3e06caf1b2b86cad1b2a86ca9238a8b01b2388d2a2c06c8e200a8b01b2387e2a2c06c8e1f4a8b01b2387c2a7986cfb1b3e46cb11b2c06caf1b2b86cad1b2a86ca91b2386c8d1b2046c7f1b1f86c7d1c4a8b01b2386d2a2c06c8e1aca8b01b238592a8246de61b7746dd91b7606dd51b7106db11b3e06cb11b2bc6cae1b2b46caa1b2a46c8f1b2346c811b2006c7f1b1f86c7d1b1c46c6d1b1ac6c5913caa4b1b7bc6de61b49c6d261b4906d231b4886cf81b2c46cb01b2bc6cad1b2a84e0b81d0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster11_ok : cluster11.all codeOK = true := by decide +kernel
def cluster12 := decodeCluster 192 [] 0x62138aa0d1b7ac6cb41b2c86c921b2446c8f1b2306c8b1b2286c891b2206c851b2106c831b2046c801b1fc6c7e1b1f46c6d1b1ac6c621b1644d2a7e86df91b2486c911b23c6c8c1b22c6c8a1b2246c881b2146c841b20c6c811b2006c7f1b1f86c7d1b1b46c6b1b1886c591b1186c42104a8921b2446c8f1b2306c8b1b2286c891b2146c841b20c6c811b2006c7f1b1f86c7d1b1b46c6b1b1886c59100a8911b2306c8b1b2286c891b2206c841b20c6c811b1fc6c7e1b1f43f2a2486c911b23c6c8c1b22c6c8a1b2246c881b2106c831b2046c801b1fc6c7e1b1f46c6d1b1643e0ece4921a244688a1a21468620e4a7211ac803829e706b131abd86ae71a8b469371a3146a741b9cc6e6c1b89c6def1b7886dc11b49c6d261b48c6d221b2c46c9e1b23c6c8c1b2046c801b1fc6c7e1b1f46c7a1b1b46c6b1b1644e2a9d06de21b2dc6cb11b2786c921b2446c8c1b2286c891b2206c851b2106c831b2086c801b1fc6c7e1b1f46c7c1b1e86c6d1b1ac6c621b1646c4e1b1346c411b1006c3f1b0f83b0dce79c1ac4c6af61ab9c6a2d1a5a069601a4dc6af11bbc06d1f1b4646d171b4586cc01b2d86caf1b2486c911b23c6c8c1b22c6c8a1b2246c881b2143b0d41d0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster12_ok : cluster12.all codeOK = true := by decide +kernel
def cluster13 := decodeCluster 192 [] 0x83208ab881be0c6f821be046f801b61c6c921b2446c8f1b2306c8a1b2246c881b2146c82204ab131b8e86e361b2446c8c1b22c6c8a1b2246c881b2146c841b20c6c821b204802af106fbf1bef86fbd1b9d46d7d1b2486c911b23c6c8c1b22c6c8a1b2206c851b2086c811b2007f2a2486c911b23c6c8c1b2286c881b2146c821b2007e2a2486c911b23c6c8c1b2286c881b2146c821b2007d2ac886dea1b7a46de81b79c6c911b2306c8b1b2286c891b2206c851b2106c831b2046c7f1b1f86c7d1f0ab171bc586f151b2446c8c1b22c6c8a1b2246c881b2146c841b20c6c821b2046c7f1b1f86c7d1b4ab101b5c46d701b5bc6d6e1b2446c8c1b22c6c8a1b2246c881b2106c831b2086c811b1fc6c7e1b1f46b2ad906f411bd006ee21b2446c8c1b22c6c8a1b2246c881b2146c841b20c6c821b2046c7f1b1f86c7d188ab671bd246f481bd1c6f201b2446c8c1b22c6c8a1b2246c881b2146c841b20c6c821b2046c7f1b1f86c7d164a8921b2446c8c1b22c6c8a1b2246c881b2146c841b20c6c811b2006c7f1b1f86c7d1b1b46c6b1b1886c5913ca8921b2446c8f1b2306c8b1b2286c891b2206c851b2106c831b2046c801b1fc6c7e1b1f46c6d1b1ac4e0ec1d0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster13_ok : cluster13.all codeOK = true := by decide +kernel
def cluster14 := decodeCluster 192 [] 0x5806937100a6f61a8b469601a4dc3f29c4c6af61a8b469681a58069370f8a7831ad403d29f746bdc1af506bca1af246bc71af186bc31af086bc11af006b9c1ae406b8f1ae386b8d1ae306b8b1ae206b791ac4c6b031ac086afc1abcc6ae71a9246a311a8b469e61a70869ae1a68869a11a5a069671a56469531a4dc69331a4bc692c1a3d068f31a31468bd1ada46f4f1bd386f4d248ab551bc8c6f211bc806f1f1bc786f1d1bc706f1b1bc686f191bc006c92244ab681bd306f4b1bd286f211b2448f2acf86f181bc486f061bbd06e321b8806cde1b3086c921b2446c8f1b2306bdb1bf646fd81bf5c6fcb1b47c6c921b2446c8f1b2308b2ad986f461bd146f141bbdc6ef41b95c6dfb1b7d46d341b2486c911b23c6c8c1b22c6c8a1ab846e2d1b8b06e2b1b8a86e291b2486c911b23c6c8c1b22c6c8a224ab651bd106f431bd086f1c1bbdc6e701b5386cc21b2486c911b23c6c8c1b22c6c8a1b224882ad886f3f1bcf46f3c1bcec6c921b2446c8f1b2306c8b1b2286c891b220852a2486c911b23c6c8c1b2286c881b214842a2486c911b23c6c8c1b2286c881b214832a9586e521b9446e501b93c6c921b2446c8f1b2306c8b1b2286c891b2206c851b210820ec1d0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster14_ok : cluster14.all codeOK = true := by decide +kernel
def cluster15 := decodeCluster 192 [] 0x97c6a5e1a85069384dca75f1a70cf8294dcf429c846b20340a720338a7211ac80cd29e0c6b502f0a7831ad40ba29e0cb929d7caf29d7c69c32b4a75f1a70caa29d7c6b211ac80a929d8c6b441a8b469641a3c468a91a2749229efc6b631ad506b4f1ad306b441ac4c6a2d1a5a069641a4d469341a4c868f11a2a4689d244a491240a6f61ab9c6a2d1a580693723ca7bf1a8b469681a58069341a4c868a91a2408c298b48b29efc6b631ad506b4f1ad306b441a8b469681a59069351a3c4689d228a74f1ad306b441ac4c689d224a7bf1ad8c6b541a8b469641a3c468a9220a7bf1ad8c6b541ad3c6b4c1ad106a2d1a5a069641a4d469341a3c468a91a2746890214a7bf1ad8c6b541ad3c6b4c1ad106a2d1a5a069641a4d469341a4c868f11a36468d61a34068cf1a33868cd1a2a48229e706b131abd86ae71a8b48129bd86960200a7131abd87f29c4c6af61f8a7131abd87d29bd86a2d1a58069371f0a75f1a70c7129bd86ae71a8b469601a4dc6d29bd86ae71a8b469601a4dc6b29d8c6b441a8b469641a3c468a91a2746229bd86ae71a8b469601a4dc5929e706b131abd86a2d1a580693713ca79c1ac4c6af61a8f46a2d1a5a069601a4dc68da138a79c1ac4c6af61a8b469601a4dc4d29d7c69c311ca7131abd86960104a79c1ac4c6a2d1001d0240801c060140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster15_ok : cluster15.all codeOK = true := by decide +kernel
def cluster16 := decodeCluster 192 [] 0xf8322a0f8302a1386c4d1b0f82e2a1386c3e0b0a84e1b0f82a2a1386c4d1b0f828098e4a21b2706c951b1c44e2a1c44d2a138372a0f835094e52d1a42c6d0a1b4246d081b41c6c9c1b2646c93138a84e0eca84e0dca84e0d4a84e0c8a84e0c0a84e1b1342e2a1382d2a1382c2a1382a2a1386c4d0a0a84e09ca84e098a84e094243985468a11b2706c991b24c6c611b17c6c581b1586c55138a84f0eca84e0dca84e1b134362a13c352a1386c400c8a84f1b1386c4d1b1002e2a13c6c4e1b1346c411b1002c2a1382b2a1386c4d0a0a84e09ca84f1b13826088e52d1a2846c9c1b2646c931b1e46c701b1b06c69138a8a11b27c6c991b1e46c761b1c06c6c134a84e1b1343b2a1343a2a1386c4d0dca84e0d8a84e1b134352a1386c4d0c8a84e1b134312a1386c4d0c0a84d0bca84e1b1342e2a1382d2a1386c4d0b0a84e1b1342b2a1386c4d0a8a84d0a4a84e1b134282a138272a1386c4d098a84e1b134250841f4813c2e0a8e44d0ec2807923c31af0bbf29e846ba01ae7c6b9e1ae779c29e278329de8678ad40a76ac84a76bc80a7601acc06b2f1acb86b2d1acb06b2a1aca46b281ac771329bf067aa1aea46ba81ae9c6ba61ae946ba41ae8c6ba21acaef629bd0675fbcca6ed1abb06aeb1aba86ae91aba2e729bdae129e72762997467d51abcc6a311a8c06a2f1a8ba2d297f865fd19d7de629799c3298b5c2298b5ae29c306b0b1ac286b091ac206b071a9396029564677f1adf86b7d4dc1d0240801c060140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster16_ok : cluster16.all codeOK = true := by decide +kernel
def cluster17 := decodeCluster 192 [] 0xf8352a138322a138302a1386c4d1b0f82e2a1382d0b0e49c1b2546c941b24c6c711b1746c50138a871134a84e1b0f8352a138302a1386c4d1b0f82e0ace6371b3ac6cc01b2886ca11b2706c951b2506c931b2206c801b1d46c711b1646c50138a871134a84e0dca84e1b134362a0f8352a138322a13c6c4e1b1346c3e0b8a84e0b02a391c44d2a2886ca11b2706c941b24c6c711b1403e2a0f8372a0f8362a0f8322a1346c3e0b829398e4692d1a8846d3f1b4a46d271b4986d241b48c6d221b3e06cc11b3006cbf1b2f86cad1b2886ca11b2786c9c1b2546c941b24c6c801b1cc6c711b1b46c5e1b1746c50138a8f81b3006cad1b2886ca11b27c6c9e1b2546c801b1cc6c711b1b46c5d1b1404d2a1386c4d0eca84d0e8a84e1b134372a138362a1386c4d1b0f8352a1386c4d0c8a84e1b134312a1386c4d0c0a84d0bca84e1b1346c3e0b8a84e0b4a84e1b1342c2a1386c4d0a828392886ca11b2546c711b1746c50138a84e0eca84e0dca84e1b0f8352a138322a138312a138302a1386c3e0b827398e4686f13ca9551b4b46d291b4906d231b3b06ceb1b3a46cad1b2886ca11b2706c9b1b2546c941b2006c711b1bc6c5d1b16c4e2a1c44d2a3b06ceb1b3a86ce91b2b46ca21b2846c9f1b2706c9b1b2506c711b1746c5b0f8a84e1b0f83b2a0f83a2a1386c3e0dca84e1b1346c3e0d8a84e1b0f8352a0f8342a138320981f0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster17_ok : cluster17.all codeOK = true := by decide +kernel
def cluster18 := decodeCluster 192 [] 0x71134a9621b4686d191b4606d161b3e86cc01b2bc6ca21b2846c9c1b2646c941b24c6c8c1b2006c711b1746c500f8a83e0eca84e1b0f8372a1386c3e0d835398e4692d1a4a069291b48c6d201b32c6cb11b2886c9c1b26c6c991b2546c941b2286c801b1c46c5d138a871134a84e0eca84e0dca84e1b0f8350c8e6391a4a069291b48c6d201b2706c991b2546c801b1c44e2a1c44d2a0f8350c4e4a21b2846c9c1b2646c951b2506c801b1c44e2a1c44d2a138372a1386c4d0d8a83e0d430391c44d0bce6391a774692d1a4a069251a92c6d7b1b4a46d241b48c6d201b2c46cb01b2bc6cad1b2b06caa1b2886ca11b2706c991b2546c941b2006c711b1744e2a5ec6cb11b2c06caf1b2b86cad1b2b06caa1b2886ca11b27c6c991b2546c801b1c46c5d134a8b11b2c06caf1b2b86cad1b2b06ca21b2846c9f1b2706c991b2506c801b1743e2a1386c4d1b0f83b2a1346c3e0e8a84e1b1346c3e0dca84e1b0f8362a1386c4d1b0f8352a0f8342a1386c4d1b0f8322a1346c3e0c02e398e469281a4a46d201b2886c991b2546c801b1c44e2a138372a0f8350b4e6391a4b4694d1b4a46d271b4986d231b4886ca41b28c6ca21b2786c9d1b2706c9b1b2686c981b25c6c951b2506c931b23c6c881b2006c781b1c46c5d1b1404e2a1c44d2a1383b2a138372a138350b01f0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster18_ok : cluster18.all codeOK = true := by decide +kernel
def cluster19 := decodeCluster 192 [] 0x48c6d20284aab81badc6eb61bad46da71b5ec6d291b4906d221b4806ca21b2849c2a2886ca11b270992a5286d491b5206d471b5186d291b49c6d261b4906d231b4886d201b2846c9c1b264952a9e46e781b9dc6d291b4906d201b2846c99250a9291b4906d201b2886ca11b2646c9524caa3a1b8e46e381b8d86d291b49c6d261b4906d231b4886ca11b2706c93200aa531b4a46d271b4986d241b48c6d221b4806cfb1b3dc6ca11b2706c991b24c712a96c6e5a1b9646e581b2846c9c1b2646c93174a9291b4906d231b4806ca11b2706c991404e393ec6cf91b3dc6ca11b27c6c991c44d39898689d124a5781a5dc69741a51468f30f8a6521aab06df51b2886c9c1b2646c951b2506c931b2306c8b1b2286c881b21c6c851b2106c831b2006c711b1886c50138a8711343b391c44d0e8e6391a4b469281aad06e6c1b89c6de21b7046d3a1b4a46d271b4986d231b4886d201b3f06cb11b2886c9e1b2706c991b2546c941b24c6c8c1b2006c7a1b1c46c5d1b1404e2a1c44d2a1383b0dce6391a4b469281a4a46d201b2646c951b2006c711b1746c50138a89f1b2546c801b1744d0d8e5621b4686d181b45c6d161b3e86cc01b2bc6ca21b2846c9c1b2646c951b2506c931b2306c801b1c46c601b1404e0d41f0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster19_ok : cluster19.all codeOK = true := by decide +kernel
def cluster20 := decodeCluster 192 [] 0x4f0d4a84e0c8a84f0b827398546a551b8dc6e341b8206dd91b7606dc41b6c46ceb1b3a46ce81b2b46c9b1b2006c6f1b1886c601b17c6c5d1b1706c5b1b1646c571b1586c551b1444f2a13c3b2a13c372a13c352a13c6c4e1b100322a13c302a13c6c400b8a84f0b4a84f1b1386c4d1b1046c3f1b0b82c2a13c2a2a13c28098e44f0eca84f0d4a84f0b82539854684f0d4a84e1b100322a13c6c400b8a84e1b1346c411b1002c2a13c2609022485d43e299483b297742e2913c6c4e0b82a391343b0a0e46f13c26391e46c701b1a46c611b17c6c5c1b1586c55100a84f1b1003b2a100372a100362a13c6c400d4a84e1b100322a100312a100302a13c6c400b8a8400b4a84f1b1386c4d1b1046c400b0a8400a8a8400a0a84f1b10026088214813c6c4e0b82a08122cc898a628700a6261a700697e4a4a6261a70121294a469213fca5291a484f12970068f1370a6261a70068ff1a3c4c72989869c02d8a52d1a4a0a2298e4692d1a4a0a1294a469211a37068c81a31c9d298e4692d1a4a09c294b495294b46928250a6391a4a0932940068ff1a3c4689d208a52d200a52d1a4a0712970068f11a27454294a0502951468f313ca6d71ab586acb1ab286ac71aad06aae1aab46aab1aa786a7c1a9a06a671a9886a611a9806a5c1a91469be1a68869a11a5fc69451a4e469361a4b069051a3d06ad51bb506ed31b88c6d291b49c6d261b48c6d221b480a22a4a46d271b498a11381f0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster20_ok : cluster20.all codeOK = true := by decide +kernel
def cluster21 := decodeCluster 192 [] 0x57c69531a4dc692f1a4b068f41a3cc68a81a29868a51a29c6c9e1b2746c9b1b2686c981b25c6c921b23c6c881b1e06c601b17c6c5d1b1706c591b15c6c561b1544f2a29c6c9e1b2746c9b1b2686c981b25c6c921b23c6c781b1886c601b17c6c5d1b1706c591b15c6c561b1544e2a8546dec1b2d06cb21b29c6c9e1b2746c9b1b2686c981b25c6c921b23c6c881b1e06c621b1806c5f1b1746c5c1b1646c571b1586c55134a9f81b7d86ca71b2786c9d1b26c6c9a1b2606c971b2486c8f1b2206c781b1886c601b17c6c5d1b1706c591b15c6c561b1546c461b108412a29c6c9e1b2746c9b1b2686c981b25c6c921b23c6c881b1e06c621b1806c5f1b1746c5c1b15c6c561b154402a29c6c9e1b2746c9b1b2686c981b25c6c881b17c6c5c1b1586c550fca84d1b1046c401b0fc3b2a1386c4d1b1046c401b0fc372a13c6c4d1b1046c401b0fc352a1386c4d1b1046c401b0fc322a13c6c4d1b1046c401b0fc302ab986ee51b2b46c9b1b15c6c561b13c6c4e1b1346c411b1006c3f1b0dc6c2e1a13c6c4e1b1346c411b1006c3f0b42c3985468400c8a84f1b1002e2a13c6c4d1b1046c3f0b02a3913c6c4d0eca84f0d4a84e1b100322a13c6c400b8a84f1b1386c4d1b1046c3f0b0283913c3b09c220240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster21_ok : cluster21.all codeOK = true := by decide +kernel
def cluster22 := decodeCluster 192 [] 0x3604f297c0693e1a41468f4138a49d12ca49d124a49d114a49d110a49d10ca5a21a684693e1a4e441297c0693e1a41468f4100a6521a854688c1b22c6c8a1b2246c881b21c6c851b2106c831b1806c5f1b1746c5c1b1646c581b15c6c561b1544f0ece66d1b8d06e0b1b76c6dd91b7606dc41b6c46d191b4606d171b4586cc01b2bc6c8c1b1886c601b17c6c5d1b1706c591b1606c571b1586c5513ca84f0dc353929c689e1a248688f1a1e0332985469f51b7d06d6c1b5ac6d6a1b32c6cba1b2c46ca21b26c6c621b1806c5f1b1746c591b1606c571b1586c55138a9f51b7d06d6c1b5a86ccb1b2e86cb11b2886c9b1b2286c621b1806c5f1b1746c5c1b1646c571b1586c55100a8400eca84e1b100372a13c6c400d4323985468400c83039bf86aef1a8cc6a0a1a77469d11a3306a341b8246df31b76c6dd91b7606dc41b6c46cfa1b2c46caf1b2b46cac1b2a86ca91b1c46c621b1806c5f1b1746c5c1b1646c581b15c6c561b1544f2a7cc6cfa1b2c46cb01b2bc6cad1b2a86ca91b1c46c621b1846c601b17c6c5d1b1706c591b15c6c561b154402a13c6c400eca84f1b100372a100362a13c6c400d4a84f1b1386c400c8a8400c4a84f1b100300b8e44f0eca84f0d4a8400c8a84f1b1002e0b4e76d1adb06b0e1ac346afd1abec6af90b0220240801c060140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster22_ok : cluster22.all codeOK = true := by decide +kernel
def cluster23 := decodeCluster 192 [] 0xc01b2c46caf1b2b46cab1b2a86ca91b2206c751b1c46c5913ca9951b3ac6cc01b2c46cb01b2b46cab1b2a86ca91b2206c751b1c46c59138a9951b6506d141b4486d0f1b3ac6cc01b2c46cb01b2bc6cad1b2a46c881b1c46c590f8a84f0eca84f1b138372a1386c3e0d8a84f0d4a84f1b1386c3e0c8a83e0c4a84f0c02e3913c6c3e0b82d3913c6c4e1b0f82e0b02a4832089298ac69ce1a40c68c4138a6e11a94868c21b3006cad1b2786c8c1b2286c891b2206c861b2146c731b1b46c621343b391343b0d4e44d0ec32391343b0c0e5dd1a1343b0b8e44d0ec2c391343b2a13c6c4e1b0f82e0a828488ac4e09ce2dc1a771012959469011a3c4c829320c629320c529320bb2940482293b86ae41b8206dd91b7606dd51b7106db11b3ac6cea1b3a46ce81b39c6ce61b3946ce41b38c6ce21b3846ce01b37c6cad1b26c6c801bca86f16ca86f1444f397384e297384d2959868f41a3b83e29b846a521a1bc4f0ece46f13c37391bc4f0d4e46f13c34391bc4f0c8e46f13c30391bc4f0bce5dd1a1bc4f0b8e46f13c2d391bc4f0b0e46f13ca84f1b1386c3e0b82a391bc4f2a1343b0a026489483b2913c6c4e1b0f82e0a8e44d0ec28391bc4f09824481382e0a82348b98661e1987465e42d8a6ee1a2d8a92956c68f11a33ca72956c9e297d868dc1a3209d293c49b2956c68f11a33c962956c68f11a33c922956c68f11a33c8f2956c68f1220a55b1a33c7829bb871292d8652985462298545d298545c2985459298545729854562985455298f8693e1a4e4692f13c220240801c060140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster23_ok : cluster23.all codeOK = true := by decide +kernel
def cluster24 := decodeCluster 192 [] 0xefc6b631ad506b4f1ad306b441a8b468f11a34068a91a2745929b844f29b8469891a40c68c4138a6e1134a6e1104a6e1100a6e10f83b3824868911a200686b1a1643b0e4e24c1a8ac69891a40c68c4138a6e11a9483b0dce24c13836387714129b9c6941320a4c82a4a5411e0a4c8168a5191b458c82a31468c41a320af2a3208c13ce5ce1a62469031a3104e2956469580f8a6e11a94868c813c3b393204f0dc3548b9cc80d0e24c1a6244e299483b293204f0d4324893069891383138b9cc8293209d297386989138a5ce134a6520eca4c813c350c1237b19ef06b71d7ca6fc19d7de629799c3295512b29d7c69c33e0a5951a65068eb320a4c8300a5dd2bca5dd2b8a5dd1a4acad29774aa29774a9293208829d7c8029d7c69c31f0a5dd1c4a75f1a70c6d29d7c69c31aca6ee180a75f1a3205929bb857297dc69421a4ac686313ca64c1a91c69ce1a6244e295084029ed46aff1ab846a521a5a069541a3303b2977468c813c3539774342977430297742f0b8e24c138a6520eca4c813c35397742e0b4e1611a334c829320a92956c68f11a33ca72956c68f11a33c922956c68f1188a55b180a4f1174a55b1a3c468cf164a5a11a56c68f11a33c572956c68f11a33c54298ac69031a3bc68c51a3104e29b846a520eca4a71a24868601a16468570cca5421a3c82e0b0e1031a3104e0ace195320a4c82c4a4c82a4a4c81c4a5ce1a40c68c4138a5ce134a6e11a9483b2977468fe1a9046e091b7686dd91b7606dc41b6c46d951b6506d131b4486d111b4406d0f1b3ac4f0b82a0240801c060140400c02c0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster24_ok : cluster24.all codeOK = true := by decide +kernel
def cluster25 := decodeCluster 192 [] 0x2a81aa9c6aa6930a6e31ab822b29acc6a22738a681624a69f500a6264a4a5ce480a66e1a86c6a181a490692040ca5293fca6481a83c6a0e1a4906920310a67a1a5f869501a50068ff1a3d868f1288a67a284a4a2274a67a270a626264a67a1a89869c01a5f869501a50068ff1a3d868f11a27495299e86a26250a67a24ca67a1a8ec6a261a70069501a3fc68f61a3c468bb1a274802989869c01a5f869401c4a6261a3fc689d174a67a1a89869401404e38891ce134e09d188a49d174a49d164a49d15c41385e576295d8a22958c7a295d871295d8500f8e377c70a778c6ca7d61ac4ee129d846b3a1ace46b381acdc6b361acd46b341accc6b32948a65290ca7d51af522d29efde629c706b1b590a71c1ac6ccf29c6cce29c706b1b334a5641a334c829c706b1b1a32068b62a4a7bf1ad8c6b541ad3c6b4c1ad106a2d1a3c468d01a2a4689d248a7bf1ad8c6b541ad3c6b4c1ad106a2d1a3c468d01a2a4689d244a7bf1ad8c6b541a8b468f11a34068a923ca6e11a9488c29b846a5222ca6e11a9488a299488929b846a52220a6e11a948852994884299488329b848229efc8129efc6b631ad506b4f1ad306b441a8ec6a2d1a59068f11a340689d200a74f1ad306b441fca7bf1ad8c6b541ad3c6b4c1ad106a2d1a3c468d01a2a4689d1f0a7bf1a8b468a91b4a7bf1ad8c6b541ad3c6b4c1ad106a2d1a3c468d01a2a4689d1aca6521883b0240801c060140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster25_ok : cluster25.all codeOK = true := by decide +kernel
def cluster26 := decodeCluster 192 [] 0x35f0b81d028095659069610ec30387cc68fa1a29c68921a180685d1a164685713c2e0b11cc80b82a0911eee1ab94688f13c2e384c066e61ab9469fc1a7cc69e51a79069611a56c693e1a4f468fa1a3c468db1a36468d61a35468d41a34c68d21a33c68ce1a33468af1a2b468aa1a2a468941a1c468651a190685b13ca5fc1a68469641a584695b1a3c468cd1a2a43b290ec382956c37290dc33292dc68820b82c0891ea51aa906aa31aa886aa11aa806a9d1a9c66b299ae68299ac9c299ac95299ac94299ac93299ac71299ac50138e26b1382e389ac4e0b4e1611a4004f2959069611a4003b0b01f47eb46bac1ab79aa296a9a9296a9a6296a9a4296a892296a891296a88c296a88a296a888296a885296a882296a880296a87c296a86d296a86b296a862296a85929d30689d13ca5aa138a5aa134a5aa104a5aa100a5aa0fca5aa0f83b386a83b0d4e3bf1ad8c6b541ad3c6b4c1ad106a2d1a5a069641a3c468d01a2f068bb1a2743b290ec390c8e1aa0ec2e38efc6b631ad506a2d1a5a069641a58469341a4c868f11a34068cf1a33868cd1a2f068ba1a2e468a90ec2c386a83b0a8e1aa0ec26386a83b088e1aa0ec21386a83b07c1d477983b0b8e3bf1ad8c6b541ad3c6b4c1ad106af41a8b468f81a2bc68ad1a2a4689d1a1c468470eca43b0e4a43b0e01d0711daa0ec1d06d1e6b1381f386a83b0741a479ac4e07ce1aa0ec1d0651daa0ec1d0611daa0ec1d05d1e6b1381f0511e6b1381f03d1e6b1381f0391e6b1381f02d1e4480ca252590a203514a2033cca313340a2eab9ca5d7195a46538193b8c828360d7298ec802959469011bc4f0240801c060140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster26_ok : cluster26.all codeOK = true := by decide +kernel
def cluster27 := decodeCluster 192 [] 0x3c468d01a33068c61a2743b290ec390c0e3bb1aee46b711adc35f29d7f5d29d7ef329d7de629d7dd429d7dc229d7cf829d7caf29d7cae29d7cad29d7caa29d7ca929d7c8d29d7c8029d7c7e29d7c7d29d7c7c29d7c7129d7c6d29d7c6b29d7c69c3164a75f1a70c4e29d7c4d29d7c4729d7c4129d7c4029d7c3f29d7c3e29e0c69510eca75f1a70c3529d7c300b8e202688a7831a5443b0b0e35f1a70c2e0a8e35f0b828383944f29e0c69510eca75f0b82638e0c69510ec2438478691d1a2744e29efc6b631ad506b441a8b469fc1a59068f11a34068cf1a33468cc1a32468c61a2a4689d0eca43b0e4a75f1a70c2e295442c088e3831a5443b29d7c2e084e2cd8d4a5c547ca6cd1a70c691f138a7831a5443b29d7c2e07c1d47809a20b0e1931a2744e295442c088e1911381f38e0c69510ec1d0711c9d104a6ee0b8a5a11a56c68f11a33c68330b02238d7c69c30b81d06d1e026882c3864c691e1a4744e295442c088e2cd8d4a5c547ca6cd1a70c69991a644691f1381f38e0c69510eca75f0b81d0691e026882c3864c691e1a474689d138a5510b02238b3635297151f29b3469991a644691f1381f38e0c69510eca75f0b81d0651e026882c38478691d1a2744e295442c088e2cd8d4a5c547ca6cd1a70c691f1381f38e0c69510eca75f0b81d0611e026882c385442c088e3831a5443b29d7c2e0741747d7c2e0741547b363529b344e07c1347d7c2e07410473944f098e2cd8d4a6cd1a6644e07c0f47809a20b0e0c80d42a383944f098e1931a478691d1382238b3635297151f29b3469991a644691f1381f38e0c3b29d7c2e0740e47b363529b344e07c0d47809a20b0e1931a478691d1382238b3635297151f29b3469991a644691f1381f38e0c3b29d7c2e0740b47809a20b0e3830ec1d0280901c060140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster27_ok : cluster27.all codeOK = true := by decide +kernel
def cluster28 := decodeCluster 192 [] 0x6458e296458a296458429b3469c34a4a6cd49ca6cd498a6cd1a70d2329b3469c3480a6b21a89469d41a74c69d21a74069cb1a4a4692047ca591288a591284a6cd1a70c6999270a6cd1a70c691f264a6cd1a70c69991a644691f254a6cd1a6649429b34699924ca6cd1a70c691f200a6cd1a70c69991a644691f1c4a6cd174a6cd1a66469911a47c50138e19113837387151f29644691f13835386444e0c8e1911383138b3635297151f29b3469991a644691f1382e38809a20b0e27a1a89869c01a54068ff1a3d868f11a2744e29320350a8e2cd8d4a5c547ca6cd1a70c691f1382838b363529b3469c31382738b3635297151f293944f29b34691f13826386444e090e2261a70069931a5f8691e1a47468ff1a3c468c61a2744e295442c088e2cd8d4a5c547ca6cd1a70c69991a644691f1382107d1fc0efca7c51ae206b871ae186b851ae138329e0ef029e0ed8298b5c229e0d8a29c146b041a57c695e1a574695c1a56951294e067831a5449229e0c6951244a7831a5448f29e0c6951230a7831a5448a29e0c8929e0c6951220a7831a5448529e0c6951208a7831a5448029e0c7f29e0c69511f0a7831a5446d29e0c69511aca7831a5446229e0c5929e0c695113ca7831a5444d29e0c6951104a7831a5444029e0c69510fca7831a5443e0ece3bf1ae0c6b311a8b469681a54469341a4c868ce1a33068c91a30c68a91a240683c0eca43b0e03538e0c69510ec3238efc6b631ad506b4f1ad306b441a8b469681a59069350ec300740901c060140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster28_ok : cluster28.all codeOK = true := by decide +kernel
def cluster29 := decodeCluster 192 [] 0x1c61a4811e29b6c69d11a73469c81a4891d2941064ef192786522274a520194a520190a5931a274622964c691e1a474602964c691e1a474689d174a5931a474689d170a51e1a474689d164a51e160a5931a478691d1a27457138e2161a79469e41a34868941a16c4f29274410ece1e41a5046865138353864c68c61a2744e297f069640ec323864c691e1a4744e0b8e30f1ac2469601a57c695e1a570695a544a55129ca551278a55126ca551258a551248a55123ca5511e0a551188a551180a551174a551164a55115ca551150a55113ca5fc1a79469e41a584695b1a4f8693d1a3c468db1a36468d61a35468d41a34c68d21a33c68ce1a33468a91a25068651a19068631a178685b1a1686853138a551134a551104a551100a5510fca5510f8a5fc1a59069611a56c68f11a33868cd1a2a43b290ec3829544352954432295442e0b0e11e13828387f0691e1a47469011a2744e297f069641a4043b295442c098e1931a2744e295442c0902247809a20b0e0e513c263864c691e1a47468631a1684e295442c0882147f886be11af806bdf1ab486ad11ab406acf1ab3acd29b36cb29b36c829b36c029b36ac29b36548d4e2cd8d5bb38f786adf1aac86a251a75069d31a74869d01a72dc547ce2cd8d49c38b3635297151f264e2cd8d4a5c547c9538b3635250e2cd8d49338b3635297151f200e2cd8d4a5c547c7138b3635174e2cd8d4a5c547c5038b486ad11ab406acf1ab3acd29b36cb29b36c829b36c029b36ac29b35bb29a20699d1a670699b1a6699929a0069926444e07c0901c060140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster29_ok : cluster29.all codeOK = true := by decide +kernel
def cluster30 := decodeCluster 192 [] 0xd8c6b541a8b468f11a2303b29ed06bb31aec46bb01aebc6af41abcc68921a244688c1a22868881a21468821a1883729d7c350b8e22d1a3c43b0b0e22d1a3c43b0a8e22d1a3c43b0a0e22d1a3c43b098e22d1a3c43b090e22d1a3c43b293c42c088e3631a8b468f10ec213889868f1138a62d1a3c43b07c1d473c42c088e1401a3c44e07ce22d1a3c43b0741c473c42c088e2261381f388b468f10ec1d06d1cf10b0223889869c01a50068ff1a3c44e07ce22d1a3c43b0741a473c42c088e2261a5004e07ce22d1a3c43b07419473c42c088e1061a36468a91a1904d084e2261a3c44e07ce22d1a3c43b07418473c42c088e22d1a3c43b07417475004e295d83e07c16475004e07c14478984e07c13475004e295d83e07c11478986940138a5760f81f03d1e261a5004e295d83e07c0e478984e07c0d4789869401381f02c0902196e61ab946a461a5e868ad1a2a4689d1a26c68971a248688c1a22c68891a22068851a21068711a17068591a15c68561a0f83b0b8e03b0b82d0b11c3b0b82c098225613c2e0b02206d583b0b82c08817560ec2e0b02203d583b0b82c0880e560ec2e0b022029596519404e513cdfe91afa06be71af986be41af8c6b6f1adb86af21ab6c6ad91aa260229809d2688e2026899238809a2278e2026889b38809a2268e2026889638809a2248e2026888f38809a2220e2026887838809a2180e2026884f38809a2134e2026884138809a2100e2026883f38809a20f8e2026883538809a20c8e2026882e0b11d191a3acc8293208829320590d4e0c80d42e38320350b42a4782069d91a76069c41a3a468e8394a4e52b4a4e526ca4e5200a4e516ca4e51444f383944f0dce0e513c32383944f0b8e202688a4e513c2c383944f0a02647809a20b0e0c80d42a383944f09824477f12d28900663f19b65932964d902964d8c2964d86294ec65301989469d11a73869c94784e0880901c060140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster30_ok : cluster30.all codeOK = true := by decide +kernel
def cluster31 := decodeCluster 192 [] 0x3c48f293c488293c478293c462293c460293c45d293c459293c457293c454293c44f293c44e293c44d293c441293c440293c43f293c43e293c43b293c437293c435293c42e0b0e0f10b02a383c42c0a0e0f10b026383c42c090224758c3e0dce0a90f835383c42c0882147b2c6aca1ab1c6abf898a6266e8a69f1a9a06a671a99540298992929899272989926298992329899202955c69561a4b069291a48068f43c4a5401a3c4a229500a1298986940270a6261a3c4992989869401a3c495298986940250a6261a500932989868f1200a6261a70069401a3d868f11c4a626174a6261a50050138e1791a5dd76295d974295d8a2295d8a1295d89c295d894295d893295d871295d8500f8e27a1a5f869501a50068ff1a3c44e295d83e0dce140138a5760f8363889868ff13835385004e295d83e0c8e14013831388984e0c0e2261a5004e295d83e0b8e1401382d383c44e0b0e2261382a389e86a261a70069501a3d868f113828388984e09ce22613826383c44e090e226138a4f10b0223889869c01a3c44e0841f47f546af31a8c46a301a8bc6a2e8b4a62d708a62d6b8a7011a56469571a558692c1a3d468f41a3ccf1298b468f1248a62d1a3c491298b468f123ca7bf1a8b468f1230a62d22ca62d1a3c48a298b468f1220a62d1a3c485298b468f1208a62d204a62d1a3c480298b468f11f0a62d1a3c46d298b468f11aca62d1a3c462298b468f1164a62d1a3c44f298b468f1138a7bf1ad506a2d1a3c44d298b468f1104a62d1a3c440298b468f10fca62d1a3c43e0ece3bf1a8b468f11a1c43b0dce3bf1ad506a2d1a3c43b0d4e35f708a559193fc68f11c4a4f113c2e07409020060140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster31_ok : cluster31.all codeOK = true := by decide +kernel
def cluster32 := decodeCluster 192 [] 0x58c932958c712958c500f8e18d1a3644e0ece18d1a4b868d9138a5630f837384b84e2958c3e0d8e1981a634691e1a3644e0d4e27a1a5f869501a50068ff1a3d868f11a318689d138a5760f83238634691e1382e383644e0b0e0d91382b3847868d9138a51e1342a3847868d9138283863468d91382438660698d1a47868d9138a51e134a49d1042238660698d1a47868d91382107d1d033644e381c43b0c8e0d913ca49b0eca6f41abcc68bc1a24868911a230688a1a22068851a20868620c82e382bc3b29d7c6af71abd86af41abcc69c31a2f068921a244688c1a21468620b8263847868d9138a51e134a5001a3403207c1d4763589299312e2940cd9138e18d1a4b868d91381f0711d8d624a5033644e38660698d1a47868d9138a51e1341f06d1d8d624a64c4b8a5033644e38660698d1a4b8691e1a3644e07c1a479e86a261a700697e1a54069401a3d8689d1381f0651d033644e3847868d9138a51e1341f0611e4c4b84e384b84e2958c3e07c164758c3e08414479312e138e12e138a5630f81f0451e4c4b84e38660692e138a5630f81f03d1d8d624a64c4b84e38660698d1a4b8691e1381f02c0902007743c43b0b82c0895540194a1401904e374144e0d422463cc3b282bc3b0dce03b0dc300b91c3b0dc2e0881d560d42e0b02206c09653d066e61ab9468ad1a26c689a1a23068571a158372913c350b82c470dc2e0b026089583b0dc320b91c3b0dc2e0b01d560ec370b81d07158370b82c0881b560dc2e0b02205d58370b82c0880a569d069e61a3e068921a24468801a1f0686b1a1643b0dc2e473e868921a17468591a15c350b82c47320370b82a4785868ce1a2a44d0ece14113c350a11cff1a3c471293c44f29bb868960d42e38bf46a4d1a55c69561a4b068f51a3d068f33c4a4f129ca4f1278a4f126ca4f1258a4f12482c08809020060140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster32_ok : cluster32.all codeOK = true := by decide +kernel
def cluster33 := decodeCluster 192 [] 0x811a1f8687d1a138684d1a12c68400eca43b0d432380ec320a8e03b0c82807c1d560ec320b8e03b0b8260741c560ec320b8e03b0c81f0741b561383b0c81f470ec320b8e03b0c81f0741a561383b0c81f470ec320b8e03b0c81f07418560ec320b81d05d584e0ec3207c13561383b0c81f470ec320b8e03b0c81f0740f561383b0c81f035584e0ec3207d1c3b0c82e380ec3207c1d02d583b0c82e380ec3207c1d0295a821aa046a801a9fc6a7d1a640698f1a6398d624e18d625833863589600e2a81aa9c6aa61aa946a9f1aa746a9c1aa6c6a9a1aa506a901aa306a8b1aa286a679312e389b86a1c1a86c6a1a1a8646a181a85c69241a48103364e18d624a503364711391d8d624a5033644e0ed1d8d624a64c4b8a5033644e0dd1e4c4b84e0d91d8d624a5033644e0d51ddd364a18d6244e3879868f81a29068921a244687c1a1b4686b1a1643b0c82e4740cd91382c4740cd91382b4740cd9138e0c80c82e0a91d033644e0a11d010f830389d469e61a3e068921a244688f1a200687c1a1b4686b1a1643b0b82647635892940cd91382447635892940cd9138e09b193644f298f068f01a130320b8e15b26ca55b0c82c38274412956c2c0982247635892940cd9138e1630f8320851e871aa18699c660a598658a5901a63c698e634a58d60ca58d600a69d1aa706a9b1aa686a901aa286a674b8a5d41a74469c91a71869291a4811e294a469241a480d929634692e1a364a229634692e1a364a129660692e270a51e1a3649929660698d1a4b8691e1a3649529660692e250a5981a4b8932947868d9200a5981a634692e1a47868d91c4a5981a634691e1a3645d29660698d1a4b8691e1404e3875069d11a7251e294789f29478952947880294785d134e1751a5d0697358ca563288a563284a563270a5632503e07c09020070140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster33_ok : cluster33.all codeOK = true := by decide +kernel
def cluster34 := decodeCluster 192 [] 0x8b0689d0ec26388b03b090e1c31a70040298b03b29bb82e297f069611a56c693e1a4f4693c1a3c468d01a33c68cd1a2a468330b0223870c69c0100a62c0ec213870c69c0100a62c0eca5611a40068d00b01f0751e2c0ec1d0711ec21381f3870c69c0100a62c0ec1d06d1ec21a6f04e07ce1c31a70040298b03b0741a47b084e07ce1c31a70040298b03b0741947efc6b631ad506b4f1ad306b441a8b4689d0eca43b0e4a75f0b81d0611e2c0ec1d05d1cc80a8260511cc80a82638b084e07c0f473202a098e2c21381f0391ec21381f02c090200701a0cf10ec2e0982202590f10ec320b81d5531437282303b290ec350c82e472303b290ec37290ec350b82607409021d0d90ec2e0b0225563468e91a2b468851a20c68821a1583b0b8e03b0b82809822562bc3b290ec350c82e472bc3b290ec350b826470ec320b8e03b0b8260881d560ec2e0982202c09655a03b0c82e4626c4f0b82c4713c2e0b0260895aac1a7d4696d1a5b0696b1a5a868cb1a2e868b11a288689c1a26c68991a25468941a24c688c1a22c68881a21c68851a21068831a20068711a18868501383b0c91c4e0ec320a11c4e0ec3209d1c4e0ec320841f56c9c6af41abcc69e61a6bc696c1a5a8691e1a3e068cb1a2e868b11a2bc68ad1a2a868a91a29068a21a26c68921a244688f1a230688b1a22868881a21468841a20c68821a204687e1a1f4687c1a1c4686d1a1ac68621a164684f1a138684d1a12c68471a100683f1a0f83b290ec37290ec350c82e470ec320b82c470ec320b82a470ec320b8284726c3b0b826470ec320b824470ec320b822470ec320b82147c9c6aac1a6bc696c1a5a868cb1a2e868b11a270689b1a24c68911a230688b1a22868881a21468841a20c68820ec3207c1d020070140400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster34_ok : cluster34.all codeOK = true := by decide +kernel
def cluster35 := decodeCluster 192 [] 0x3b0b82c07c1d562443b290ec2e0b01d06d58910eca43b0b82c0741a562443b290ec2e0b01d06558910eca43b0b82c07417562443b290ec2e0b01d05158910eca43b0b82c0740f562443b290ec2e0b01d03958910eca43b0b82c0740b562443b290ec2e0b01d02959131a44869101a43c68e91a3a0c829320c029320ad293209b29320882932080293205b2932059293205129320372932032293202e293202d0a826473202a0982447bb8400b8e15b1a0cc2c0a0e2ee0b8a4f10b0260891cc80a8260851ec91ab206ac71ab186ac51ab106ac3b08a6c2af4a6aa1aaa469be1a6f5bc29b0869bc6e0a5bc6cca6c21a6f12929b092729b092629b0869bc48ca6c228ca6c21a6f09c29b0869bc254a6c2250a6c224ca6c21a6f08029b0869bc1c4a6c2174a6c21404e38b084e0d4e2c21383038b084e0b8e1401382c383202a098e2c21382238b0869bc1382107d1df270ca5c3708a5f11a709c02970dbb29701ba2970db629701b5294e065c0234a5c3204a5c31a700802970c69c01b4a5c31a7006b2970c69c01644038f4c6bd21af3c6bcc1abd86ae11a8c62c298b1bf298b1ac298b092298b091298b08f298b08c298b08b298b08a298b088298b085298b082298b081298b080298b07c298b06d298b06b298b062298b059298b04f298b04e298b04d298b04129efc6b631ad506b4f1ad306b441a8b469641a3c468d01a33c68ce1a33468a91a27440298b03f298b03e0ece22c0ec373870c69c0100a62c0ec3538700400c0e35f1a70c69c0100a62c0ec2e384e064bc1a2e868b9274a5611a34068ce1a33468a913ca49d0f4a7bf1ad8c6b541a8b469641a58468f11a34068ce1a33468a90eca43b0e0a4ce1a2a468380dca4ce1a2a468380d4a5611a34030292f02e0b0e3440ec2607409020070180400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster35_ok : cluster35.all codeOK = true := by decide +kernel
def cluster36 := decodeCluster 192 [] 0x3b0dc2e07418560dc68350b82c07417560dc2e0b01d05558350b82c07414560dc2e0b01d04158371a0d42e0b01d03958371a0d42e0b01d02d58371a0d42e0b01d02809021d0d819314652029ca520278a520274a52026ca520268a520260a52025ca520248a5201e0a520188a520180a52017ca520174a520170a52015ca520158a5201544e384804e0dce12013832384804e0b8e1201382d0b022569bc6a421a84069df1a77869ca1a6d0694f1a4b469271a49869231a48869131a44869101a43c68eb1a3a468e81a30068ad1a26c68881a200685b1a1646851138a44e0dca44e0c8a44e0b8a44e0b42a0991c4e0a8260911d201382c0891c4e0a8260851c4e0a82607c1c564804e0b02206959201382c08819564804e0b022471382a0981c05159201382c0891c4e0a8260700f564804e0b022471382a0981c03959201382c0880b02594d813ca0ad13c2e0b11c4f0b82c0a11c4f0b82c0982256d546b261ac946b231ac806b1f1ac786b1d1ac6c6b1a1ac646b001ab74697a1a278689d1a26c689a1a26068971a2586892244a49123ca491230a49122ca491228a491224a491220a491214a491210a49120ca491208a491204a491200a4911fca4911f8a4911f4a4911f0a4911e0a4911b4a4911aca491188a491164a491138a491134a491104a4910fca4910f83b382443b0d4e0910ec3038bd06af31ab986ae51ab7469e61a5e868f81a2bc68aa1a2a4689e1a274689b1a26868981a25c68961a24868911a23c688c1a22c688a1a22468881a21468841a20c68821a20468801a1fc687e1a1f4687c1a1e068711a1b4686b1a18868591a138684d1a11c68411a0fc683e0eca43b0d4a43b0c02e382443b290ec2e0b42c472443b2913c683b0b82c0891c910eca43b0b82c0851c910ec2c07c1d020070180400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster36_ok : cluster36.all codeOK = true := by decide +kernel
def cluster37 := decodeCluster 192 [] 0x2026802c3898c69971a61c691c138a51c1341f38f646a2b1a69c3b2984c2e0741947d5a130b8e2026802c38530691c138a51c1341f38f646a2b1a69c3b2984c694c0b81d0611c9d104a6ee0b8a5a11a56c68f11a33c68330b02205d1e639304e3898c4e07c1647d5a130b8e2130b81d0551e639304e3898c4e07c144798e4c138e2631381f0451f5684c2e3884c2e074104798e4c138e2631a65c4e07c0f4798e4c2962587138e35684c2e38809a00b0e2631a65c69871a4704e07ce3d90eca6130b81d0391e63930a58961c4e38d5a130b8e2026802c3898c69971a61c691c1381f38f643b2984c2e0740b47d5a130b8e2026802c38f643b2984c2e0740a0240801c0601648d90ec2e0b01d55314410b022461003b0c82e4722068400ec2e380ec2e0b0e03b0b82a0981d560ec320b8e03b0b826074180240801e0eda199a86669199a06667199986665199914028500a7285009e285009b285009a28500982850097285009228500782850062285005d285005c285005728500562850055138dd40138320b022555004e0b02207155401382c08819555004e0b02205155401382c0880e555004e0b02202c09643c43b0b82c07554400ec370b91ee61ab946a741a79869e21a3e068b71a2bc68ae1a2a868a91a280689e1a26c68981a25c68961a234688c1a22068801a1f8687d1a1f0687a1a1e068711a1ac68591a13868471a104683f1a0f83729bc86af11abc06ae61ab946add1a79869ad1a46469171a45868f81a30868b61a2c468af1a2a868a91a26c689a1a26068971a258688f1a23068881a200687f1a1f8687d1a1f068781a1c4686b1a18068591a13c684e1a11c68411a0fc683e1a0ec35290d432290dc68350c02e0b11c350b82c0911c370b82c0891c371a0d42e0b01f07558350b82c0741c560dc68350b82c0741b560dc68350b82c07419024080180400c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster37_ok : cluster37.all codeOK = true := by decide +kernel
def cluster38 := decodeCluster 192 [] 0xf647f29f646a2b1a69c4f29f646a2b1a69c4e29f646a2b1a69c4d29f646a2b1a69c4129f646a2b1a69c4029efc6b631ad506b4f1ad306b441a8b469641a3c468d01a33c68ce1a33468a91a2743f29f646a2b1a69c3e0ece22b0ec3738f646a2b1a69c3b0d4e3d90ec3238f643b0c0e35fd74a75e1ad706b5b1ad6a132984de629ec869e6530a6131a530af2984cae2984c694c2b4a6131a530aa2984ca92984c8d2984c7e2984c7d2984c694c138a6131a5304d2984c694c11ca613104a6131a5304029d7c69c30fca6131a5303e29f646a2b1a69c3b2984c694c0d4a6130c02e38f646a2b1a69c3b0b0e3d91a8ac69a70eca6131a5302e0a8e22b0eca6131a5302e0a0e3d91a8ac69a70eca6130b826384c065ed1a79068d31a348685b13ca5fc1a34068cd1a2a44e2927441297b469e41a3484029efc6b631ad506b4f1ad306b441a8b469fc1a59068f11a34068cd1a2a4689d0eca43b0e4a43b0e0a4a91a0e035297f068d00c8a75f1a7dc68cc0b8a5fc1a584695b1a3c468d01a33c68ce1a33468a91a0cc2c297f069011a34068c50982238efc6a2d1a33868a90eca43b0e0a75f1a70c2e084e0c60881f0751e63930a58961c4e38809a00b0e2631a61c69521381f38f646a2b1a69c3b0741c4762587138e35684c2e38809a00b0e1971a61c69521a4704e294704d07ce3d91a8ac69a70eca6131a5302e0741b4798e4c2962587138e35684c2e38809a00b0e2631a65c69871a548694c1a4704e07ce3d91a8ac69a70eca6131a5302e0741a4798e4c2962587138e35684c2e06409020070180500c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster38_ok : cluster38.all codeOK = true := by decide +kernel
def cluster39 := decodeCluster 192 [] 0x13830291382e291382d291382a29138282913827291382629138250901f071584f0b82c08817561382407c1c051584e0901f07013561382407c1c03d584e0901f0700e561382407c1c0355aa81aa9c6aa61aa646a981aa5c6a961aa5663930e2811a62d89296258861c4e47625871383b4798e4c2962587138374798e4c138364762587138354798e4c2962587138324798e4c29625871383147625871383047dd46b741adcc6b721ad786b5c1ad6c6b5ad5a1338d5a132bce35684cae38d5a132b4e35684caa38d5a132a4e263930a75684ca58961c4e38d5a13134e35684c4738d5a13104e35684c4038d5a130f8e35684c3538d5a130c02e4798e4c1382d47fa06be51af8c6b91809a038809a0278e2026809b38809a0268e2026809638809a0220e2026807838809a013ce2026804e38809a0134e2026804138809a0100e2026803e38809a00ece2026803538809a00c8e2026803038809a00b82c47d5a130b8e2026802c0a91f5684c2e0a11f5684c2e38809a00b0264780cc6088dd630f8240851e991aa606a971aa586a9598ca6851aa106a8365ca58b1a621872992952299ec69b91a6dd4c29531292953123295312029ac469cc1a4a46920470a6631a61c6952284a6631a65c694c270a54c1a470992998c699724c4e3873d1c294709f134e1871a5484e0ece2631a61c6952138373898c4e0d8e1971a61c69521a4704e0d4e2631a61c4e0c8e2631a61c4e0c4e1971a61c691c138a51c134303898c69971a61c691c1382e3898c4e0b4e11c138a51c1342a38530691c13828385304e09ce11c138a51c13426389e8697e1a54069401a3fc68f61a3c4689d138a5760f824383184f2989868ff1a2744e2927441293c42c0881f47f6bd929f6711298c22d29b8c6aac8aca7ab69ca7d91a8ac69a7244a7d91a8ac69a7230a62b22ca7d91a8ac69a7228a7d9224a7d91a8ac69a7220a7d91a8ac69a7214a7d91a8ac69a7208a62b2043b07409020070180500c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster39_ok : cluster39.all codeOK = true := by decide +kernel
def cluster40 := decodeCluster 192 [] 0xd42e0b02205d584d0902106015561342408418051584d0902106010560dc2e0881d47134240841803809021d0c41382c0891a62194f86529284a529270a52924ca529184a52917ca529170a529158a5291544e384a44e0dce12913836384a44e0c8e12913831384a44e0b8e1291382d386ac694d1a4a469271a49869231a48868a71a29068a31a288689e1a274689c1a26c689a1a26068971a25468941a24c68921a20068781a1c468621a180685f1a174685c1a16468571a15868551a1404e29138372913832291382e291382d0b0e129138a44e0b028384a44e291382c0982207d59721a248892922488292247c29224592922457292243e0ece2f41a5c868fa1a3e068b11a2b468aa1a2a468921a22468881a210687c1a16468571a11c683e0ec2e380ec2e0b4e0a71a278689d1a26c689a1a26068971a25868921a244688c1a22c688a1a22468851a21068831a20868811a200687f1a1f8687d1a1f068781a1b4686b1a180685f1a174685c1a15c68561a15468541a13468411a0f83b290ec2e290ec2d0b0220755929138a44e0b02207c1c564a44e291382c0881f470ec2c0881d0695929138a44e0b02207d1c3b0b02207419564a44e291382c0881f06159291382207c16564a44e291382c0881f470ec2c0881d05159291382207c11564a44e291382c0881f470ec2c0881d03d5929138a44e0b02207d1c3b0b0220740e564a44e291382c0881f470ec2c0881d02d583b0b0220740a02595da13c2e0b0225613c2e0b02207d584f0b82c0881d569c86a421a78469df1a77869ca1a6d0694c1a52c69291a49c69261a48c69221a480690b1a42869091a42069071a288689c1a26468941a24c688f1a200687a1a1c468621a1746850138a44e0d42407c1c020070180500c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster40_ok : cluster40.all codeOK = true := by decide +kernel
def cluster41 := decodeCluster 192 [] 0x2c468a21a270689b1a26468951a25068931a20068711a18868601a17c68591a16068571a15868551a1404e29138370c8e04e0c82c38138320a0e04e0c8270881f560fc3b0c82e470fc3b0b82647c9c69f51a7d069f31a79869721a5b0696a1a47868fa1a3e068cb1a2e868b11a2bc68ad1a2a868a91a290689b1a23c688a1a204687e1a1f4687c1a1b4686b1a18868601a17c68591a15c68561a15468541a13c684e1a134684b1a11c68401a0f8683b1a0dc68350c82e380c82e0b0e0320b82a380c82e0a0e2751a9546a371a7cc69e61a3e868f81a3b068eb1a3a068b11a2c068af1a2a868a91a26c688f1a23868801a1f8687d1a1f0686f1a1b4686b1a18868611a180685b1a15c68561a15468541a144684f1a138684d1a11c68451a0f8683b1a0dc68350b8260891c3b0c82e380ec2e09821075584e0c82207d1c320b8a42e098220741c560c82e290b8260881d06d584e0c82207d1c320b8a42e098220741a56138320881f470c82e0881d061582e098220741656138320881f04d582e098220741156138320881f470c82e0881d03d584e0c82207c0d56138320881f470c82e290b8260881d02d58320b8a42e098220740a0240801e0cf10ec2e0881d02590350b82c0881f560fc3b0dc2e4770469721a3e868f81a2c468aa1a2a4687c1a17068591a15c68471a0f8370b8e0350b82c380dc2e0a822075591c1a438690d1a430690a1a42069071a37468b51a2d068b21a288688f1a1ec687a1a1d868741a1c468701a1b8686d1a1a868691a19c68661a1886860134a44d0eca44d0c8a44d0c0a44d0bca44d0b0a44d0a8a44d0982408418024080180500c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster41_ok : cluster41.all codeOK = true := by decide +kernel
def cluster42 := decodeCluster 192 [] 0x2448828244852824484282448328244822824481282447f282447e282447d2824478282445f282445c28244562824455282444d2824441282443e0ecdc910ec2e372443b0b42c0881d642443b0b0220741a642443b0b02207419642443b0b02207414642443b0b0220740f642443b0b0220740e642443b0b0220740b642443b0b0220740a645a0679b1ae686b991ae606b971ae586b951ae506b931ae486add1a804a72929c9e29b746a021a73469a21a684699f1a67869721a29c689e274a4a71a2749b2929c689d268a4a7260a4a725ca4a71a274962927492292748f2929c689d220a4a7204a49d200a4a71a2747f2929c7e2929c7d292747c2929c689d1e0a49d1b4a49d1aca49d188a49d180a4a717ca49d174a4a71a2745c292745929274572929c562929c5529274542929c689d13ca4a71a2744e2929c689d134a4a71a274412929c689d0f8a4a70dca4a71a274352929c689d0c8a4a71a2743029b986ae51ab7469f31a79869721a3e868f81a2c468af1a2a868a91a29c689e1a274689b1a26868981a25c68961a248688f1a22068811a200687f1a1f8687d1a1f068781a1b4686b1a18868601a17c685d1a17068591a15c68561a15468541a13c684e1a13468471a104683e1a0dc68351a0c868300b8a4a71a0b82d0b02207558a71a274682e0b0220741c5629c689d1a0b82c0881d06d58a71a274682e0b0220741a5629c689d1a0b82c0881d06558a71a0b82c0881d05158a71a0b82c0881d03d58a71a274682e0b0220740e5629c689d1a0b82c0881d02d58a71a274682e0b0220740a0240801c069236437283c4320b8dcf10b8260881d0240873310410b022467d469f41a5b4696c1a5ac696a1a32c68ba138320881f0240801c0500c02b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster42_ok : cluster42.all codeOK = true := by decide +kernel
def cluster43 := decodeCluster 192 [] 0x2b91a604691b1a3584e0d4e1d61a6044e0c8e1d61a6044e0c4e2b91a604691b1383038ae469d61a604691b1382e387584e0b4e0f01a3584e0b0e0d61382b38ae4691b1a3584e0a8e2b91a6c8691b1a3c068d61382838ae469b21382738ae4691b138263860468f01a3584e090e2b91a604691b1a3584e293c02c088e2b91a6c869811a46c68f01a3584e0841f47f446bd01af222a298a868f0248a62a1a3c091298a868f023ca62a1a3c08c298a88b298a868f0228a62a1a3c088298a868f0208a62a204a62a1a3c080298a868f01f0a62a1a3c06d298a868f0188a62a1a3c059298a868f013ca62a1a3c04e298a868f0134a62a1a3c041298a868f0100a62a1a3c03f0ece22a1a3c03b0dce22a1a3c03b0d4e3581ad5c6b531ad4b5129d46fa29d45e629d44f829d44af29d44ae29d44ad29d44a929d448d29d448029d447e29d447d29d447c29d447129d446d29d445929d444e29d444d29d444729d444129d444029d443f298a868f00eca7510d4a7510c02e388a868f00ec2c388a868f00eca7510b82a388a868f00eca7510b828388a868f00eca7510b826388a868f00ec24388a868f00eca7510b8a4f00b022388a868f00eca7510b82138ae469b21a46c68f01a3584e298a868f00eca7510b81f0751cd91a2a468641341c0611dd61381f0591f510b81d0551dd61381f0511eb91381f04d1dd61381f0451f510b81d0411eb91a7584e07c0f47ae469d61a604691b1381f38d442e0740e47ae44e07c0d47d442e0740a0240801c0601404a13c42e0b02207409021cf5519c98672519c90672319c7c671e19c74671a19c64670019b746646195e864a719278649d1926c649a1926064971925891282448c282448b282448a28244890ec2c0881d01c0600c02a0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster43_ok : cluster43.all codeOK = true := by decide +kernel
def cluster44 := decodeCluster 192 [] 0x1b00d4a7590c02e388a4684c0ec2c388a4684c0eca7591a6c02e0a8e2291a1303b29d6469b00b828388a4684c0eca7590b826388a4684c0ec24388a4684c0eca7591a6c02e291302c088e2291a1303b29d6469b00b821388a4684c0eca7590b81f0751c8013c4e381302c088e2031381f388a4684c0ec1d0711c8013c4e381302c088e2031381f388a4684c0eca7591a6c02e0741b472004f138e04c0b0223880c4e07ce2291a1303b29d6469b00b81d0691c8013c4e381302c088e2031381f388a4684c0eca7590b81d0651cd91a2a4686413c4d381302c088e2031381f388a4684c0eca7591a6c02e07418471302c088e2291a1303b29d6469b00b81d05d1f590b81d0551c8013c4e3880c4e07c1447d642e07410472004f138e2031381f03d1c8013c4e3880c4e07ce3590b81d0391c8013c4e3880c4e07ce3590b81d02c09020070180501003b0230687d1a1f03b0741a061583b0741a06014560ec1d06818028090200701a48f029ca4f0278a4f026ca4f0258a4f0248a4f023ca4f0220a4f0188a4f0180a4f0174a4f0164a4f0150a4f013ca4f0138a4f0134a4f0104a4f0100a4f00fca4f00eca4f00dca4f00d4a4f01a3582e0b0e0f00b02a383c02c0a0e0f00b026383c02c09022473c02c0882147b046abe1aaf06abb1aaeab929ae67229a4c6a921aa446a8f1aa386a8d758a67e1a6146982604a6b91a6c92929ae52729ae52629ae469b248ca6b91a6c92029ac06aaf1a71c69291a4811b294a469203c0a5291a4906920358a5d61a60468f01a358a22975869811a358a129ae469d61a6c89c29ae469b21a46c68f01a3589929ae469d6250a6b91a7589329ae469b21a46c68f01a3588029ae469d61a6c869811a46c68f01a3587129ae469811a46c68d6174a6b91a75869811a46c50138e1811a3584e0ece1d61a60468f01a3584e0dce1d61383607c09020070180501002b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster44_ok : cluster44.all codeOK = true := by decide +kernel
def cluster45 := decodeCluster 192 [] 0x8d869ee1a4a868f81a38868a42004f1391d3b194d86530193f44e0f8dc8013c4e0ed1c8013c4e0dd1d411a408b613ce1411a2004f138e1411383e0d51c8013c4e0c91c8013c4e0c11c8013c4e0b91c8013c4e0b51cd51a35068d31a3483f0f82c474044f138e1011383e0991e3c1a79469e41a34c68d21a2ec68ba1a16c4f138e09d13ca49d138413879068651a1904d100e0a71a278689b1a248688f1a22068781a18868601a17468591a15c4c291303b29130372913035292e0684c0b82c381302c0a8e04c0b028381302c098e04c0b0240891cd91a2a4685a1383e381302c088214781c6a061a8146a0480ca6035f0a603288a603270a603254a603250a60324ca603200a6031c4a603174a603140a5441a40068ff1a3c468f01a31868c41a2ec689d1a16c685213c4e38898689d138413889869c01a3fc68f11a2744e100e2261a70069001a3fc68f11a31868c41a2ec689d1a16c68521383e3880c4e0ece203138373880c4e0d4e203138323880c4e0c0e2031382e3880c4e0b4e2031382c3880c4e0a8e203138283880c4e098e04c0b02207d1cd91a35868d01a33c68ce1a33468a913c4e38f386bcd8a4a6297e8a629248a629244a62923ca629230a62922ca629228a629220a629214a629204a629200a6291b4a6291aca629188a629164a4921a244688f1a230688a1a22068851a200686d1a1ac68621a1644c0ece2291a1303b0dce2291a1303b0d4e3ba1aee06bb71aedb5929d660929d65e629799b029d6469b03e0a7591a6c0af29d64ae29d6469b02b4a7591a6c0aa29d64a929d648d29d648029d647e29d647d29d6469b01c4a7591a6c06d29d6469b01aca7591a6c059298a4684c0eca7590d42e07409020070180501003b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster45_ok : cluster45.all codeOK = true := by decide +kernel
def cluster46 := decodeCluster 192 [] 0xa919194646413c4e0b022554f8653d194f064db1935496288f8653e194e4652f193604f138dd3e194e44e104dd3e194144e100dd3e1383e37230688b1a22868891a22068851a21068831a180685f1a174685c1a16468571a158685513c4e0ed1c4f1383b0b91c4f1383b0b51ca71a278689d1a26c689a1a2606897258a496248a4961e0a496188a496180a49617ca496174a496170a49615ca496158a496154a4a71a278689d1a26c689a1a26068971a24868781a180685f1a174685c1a15c68561a1544f138e0a71a278689d1a26c689a1a26068971a24868781a18868601a17c685d1a17068571a1586855138413829c689e1a274689b1a26868981a25c68921a1e068621a180685f1a174685c1a15c68561a1544e100e0a71a278689d1a26c689a1a26068971a24868621a180685f1a174685c1a15868551383e382584e29138412913840291383e0dce096138a44e104a44e100a44e0f83238258684f138a44e104a44e100a44e0f82e38258684f138a44e104a44e100a44e0f82d0b11c4f1383b0a11c4f1383b09822562584e291384129138400b022071584f1383b38258684f138a44e104a44e1002c0881a5613c4e0ece0961a13c4e291384129138400b022065584f1383b088185613c4e0ece0961a13c4e29138412913840291383e0b022051584f1383b38258684f138a44e104a44e100a44e0f82c0880f5613c4e0ece0961a13c4e29138412913840291383e0b022039584f1383b38258684f138a44e104a44e1002c0880b025945413ca44f138a44f134a44f11ca44f104a44f0fc2e0b0225680d442880cff2880cf12880cf0284dc6505320a203318a20316ca0fd198e86a372004f13809020070180501003b0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster46_ok : cluster46.all codeOK = true := by decide +kernel
def cluster47 := decodeCluster 135 [] 0x28868a11a27068941a24c68711a1404e0f8e04e0f837381383e0d8e04e0f832381383e0c4e04e0f82e381383e0b41f061584e0f81f06016561383e07c18051584e0f81f06011561383e07c1803d584e0f81f0600e0240801c0601404b080cc613822453184f1382207c096480c602880c5f2880c592880c572880c562880c55138de031382e3780c4e0a0de0313826089194c1a42c690a1a42069071a288689c1a25068931a23c68801a1e868711a188685d1a1404e0f8e04e0f83b381383e0dce04e0f835381383e0c8e04e0f830381383e0b8e04e0f82d381383e0b0e04e0f82a381383e0a0e04e0f8260911ca21a27068951a25068931a20068711a18868601a17c68591a15c68561a154685013c4e3813c4e0dce04f138323813c4e0b8e04f1382c3813c4e0a0e04f138260881f5613c4e0881f0715a03138223713c4e0881f0695a03138223713c4e0881f0655a03138223713c4e0881f061584e0f82407c145680c4e088dc4e0f8243813c4e0881f03d5a0313822371383e090e04f1382207c0e5680c4e088dc4f1382207c0b0240801c0601684d813c4e0b022545a06537138403724868911a23c688c1a22c688a1a22468851a21068831a20468801a1fc687e1a1f4686d1a1ac4e1003b47138400ec3747138400ec3247138400ec2e47138400ec2d075584e1003b0741c56138400ec1d069584e1003b0741956138400ec1d051584e1003b0740f56138400ec1d039584e1003b0740b0240801c06927f06561194f8653d1936c64d91935864d51933c64ce193344f1382c088070180501003a0
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem cluster47_ok : cluster47.all codeOK = true := by decide +kernel
def clusters : List (List Nat) := [cluster0,cluster1,cluster2,cluster3,cluster4,cluster5,cluster6,cluster7,cluster8,cluster9,cluster10,cluster11,cluster12,cluster13,cluster14,cluster15,cluster16,cluster17,cluster18,cluster19,cluster20,cluster21,cluster22,cluster23,cluster24,cluster25,cluster26,cluster27,cluster28,cluster29,cluster30,cluster31,cluster32,cluster33,cluster34,cluster35,cluster36,cluster37,cluster38,cluster39,cluster40,cluster41,cluster42,cluster43,cluster44,cluster45,cluster46,cluster47]
theorem addr_ok {p : List Nat} (h : p∈clusters) : p.all codeOK=true := by
  simp only [clusters,List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact cluster0_ok
  · exact cluster1_ok
  · exact cluster2_ok
  · exact cluster3_ok
  · exact cluster4_ok
  · exact cluster5_ok
  · exact cluster6_ok
  · exact cluster7_ok
  · exact cluster8_ok
  · exact cluster9_ok
  · exact cluster10_ok
  · exact cluster11_ok
  · exact cluster12_ok
  · exact cluster13_ok
  · exact cluster14_ok
  · exact cluster15_ok
  · exact cluster16_ok
  · exact cluster17_ok
  · exact cluster18_ok
  · exact cluster19_ok
  · exact cluster20_ok
  · exact cluster21_ok
  · exact cluster22_ok
  · exact cluster23_ok
  · exact cluster24_ok
  · exact cluster25_ok
  · exact cluster26_ok
  · exact cluster27_ok
  · exact cluster28_ok
  · exact cluster29_ok
  · exact cluster30_ok
  · exact cluster31_ok
  · exact cluster32_ok
  · exact cluster33_ok
  · exact cluster34_ok
  · exact cluster35_ok
  · exact cluster36_ok
  · exact cluster37_ok
  · exact cluster38_ok
  · exact cluster39_ok
  · exact cluster40_ok
  · exact cluster41_ok
  · exact cluster42_ok
  · exact cluster43_ok
  · exact cluster44_ok
  · exact cluster45_ok
  · exact cluster46_ok
  · exact cluster47_ok
theorem catalog_solved {p : List Nat} {c : Nat} (hp : p∈clusters) (hc : c∈p) : ∀ q, q≤c%16+1 → ¬Live false target q (fromAddresses c) := closedCode (List.all_eq_true.mp (addr_ok hp) c hc)
end PEqualNP.Outside.L_meta_9822.Ranked

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
def rowLo (x : Nat) : Row := Fin.ofNat 1024 (x%1024)
def rowHi (x : Nat) : Row := Fin.ofNat 1024 (x/1024)
def clash (ws : List Sig) (T a b : Sig) (d v : Nat) :=
  let r := rowLo v
  let s := rowHi v
  (bit r T != bit s T) && (bit r (bin d a b) == bit s (bin d a b)) &&
    ws.all (fun w => w==a || w==b || bit r w==bit s w)
theorem clash_sound {ws T a b d v} (h : clash ws T a b d v=true) :
    bit (rowLo v) T ≠ bit (rowHi v) T ∧
    bit (rowLo v) (bin d a b)=bit (rowHi v) (bin d a b) ∧
    ∀ w∈ws, w≠a → w≠b → bit (rowLo v) w=bit (rowHi v) w := by
  simp only [clash,Bool.and_eq_true,bne_iff_ne,beq_iff_eq,List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw ha hb
  simpa [ha,hb] using h.2 w hw
def cherryHint (ws : List Sig) (rs : List Nat) (a b : Sig) (d : Nat) :=
  let i := ws.idxOf a
  let j := ws.idxOf b
  let p := max i j
  let q := min i j
  let v := rs.getD (p*(p-1)/2+q) 0
  let e := if i≤j then d else flipOp d
  (v >>> (20*e)) % (2^20)
def gateClosed (ws : List Sig) (T a b : Sig) (d : Nat) (rs : List Nat) :=
  let z := bin d a b
  (ws.contains z || decide (z=zero) || decide (z=one)) || clash ws T a b d (cherryHint ws rs a b d)
def terminalCheck (u : Bool) (ws : List Sig) (T : Sig) (k : Nat) (rs : List Nat) :=
  (decide (ws.toFinset.card=k+1) && !(ws.contains T)) &&
    ws.all (fun a => ws.all (fun b => a==b ||
      (List.range (if u then 4 else 2)).all (fun d => gateClosed ws T a b d rs)))
theorem terminal_sound {u ws T k rs} (checked : terminalCheck u ws T k rs = true) :
    ∀ q, q≤k → ¬Live u T q ws.toFinset := by
  simp only [terminalCheck,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',
    List.contains_eq_mem,List.all_eq_true] at checked
  intro q hq run
  have width := kwWidth run
  have size := checked.1.1
  have full : q=k := by omega
  cases q with
  | zero =>
    obtain ⟨eq,_⟩ := run
    have mem : T∈ws := List.mem_toFinset.mp (eq ▸ Finset.mem_singleton_self T)
    simpa [mem] using checked.1.2
  | succ t =>
    obtain ⟨U,a,b,d,hd,eq,ha,hb,ab,fresh,tail⟩ := run
    have az : a∈ws := List.mem_toFinset.mp (eq ▸ Finset.mem_insert_self _ _)
    have bz : b∈ws := List.mem_toFinset.mp (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have ds : d < (if u then 4 else 2) := by
      rcases hd with hl | ⟨hu,hl⟩
      · cases u <;> simp <;> omega
      · simp [hu,hl]
    have test := checked.2 a az b bz
    rcases Bool.or_eq_true_iff.mp test with bad | good
    · exact ab (beq_iff_eq.mp bad)
    have hit := List.all_eq_true.mp good d (List.mem_range.mpr ds)
    have goodZ := live_proper tail _ (Finset.mem_insert_self _ _)
    have no : bin d a b ∉ ws := fun h => fresh (eq ▸ List.mem_toFinset.mpr h)
    have cert : clash ws T a b d (cherryHint ws rs a b d)=true := by
      simpa [gateClosed,no,goodZ.1,goodZ.2] using hit
    obtain ⟨different,same,others⟩ := clash_sound cert
    have remaining := kwWidth tail
    have nz : bin d a b ∉ U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    rw [Finset.card_insert_of_notMem nz] at remaining
    have s : (insert a (insert b U)).card = k+1 := eq ▸ size
    have noA : a ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at s
      have := Finset.card_insert_le (a:=b) (s:=U)
      omega
    have noB : b ∉ U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at s
      have := Finset.card_insert_le (a:=a) (s:=U)
      omega
    obtain ⟨w,hw,ne⟩ := live_row_difference tail different
    rcases Finset.mem_insert.mp hw with rfl | h
    · exact ne same
    · have hraw : w∈ws := List.mem_toFinset.mp (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      exact ne (others w hraw (fun e => noA (e ▸ h)) (fun e => noB (e ▸ h)))

abbrev TerminalPage := Nat × List Nat × Nat × List Nat
def termState (s : TerminalPage) := liveList s.2.2.1 (s.2.1.foldl (fun bank d => bank++[child bank d]) raw)
def termPage (s : TerminalPage) := terminalCheck true (termState s) target s.1 s.2.2.2
def reaches : List TerminalPage := [(10,[1188,3392,1317,1254,1319],32094,[3549850949885973562435,5911043207324733805575,3549857714087950027783,5911051096328195019783,3549865603091411241991,47288246473758429414665,5911101811350391755783,3549993020184417274887,18917226216424707473432,47288345658597937553464,5911322703446802437127,3550137210210018659335,18917425695527868055576,47288238857476020150328,154882332432264701545667,5911051096328195019783,3549865603091411241991,303717588763899513275657,1200191286295727702016,154882486619820043406531,10930885130668545680649,5911046587228858881031,3549863345796185852935,47261729271455890292753,18909101662154997661729,94540734332442250330129,321140538534096742137873,866696637664198656,5911069128353250284551,3549883635116466506759,18917190152408889573400,170798448476088638152728,154882484893653861024432,10931011671658319725232,1218639192708568254145,18909119658978517729297,5911101811350391755783,3549990700146163190791,18917226216424707473432,47288345658597937553464,3619020602960892657664,10931462013668782801568,643017183248575906711073,18909155758195870810129,643016767807973399991429,5911246067794542859271,3549990700593813916679,18917298344524928532504,47288306337244562628664,81688095073342223158339,10930926689459296605381,99414193403487428543521,18909678123044874240017,114185508702468050064581,6056302440019168117296]),
(10,[1188,3392,1317,1254,2474],23518,[3549850949885973562435,5911043207324733805575,3549857714087950027783,5911051096328195019783,3549865603091411241991,47288246473758429217873,5911101811354623808519,3549848764258853063687,18917139498968026202136,47288231884391313350712,5911034330061187585031,3549990700148178553863,18917141823547156480024,47288234208896333422648,3619026378836203801667,5911322703446802437127,3550137210210018659335,18917425695527868055576,47288238857837721198648,3619031027708804992067,6056307088449896191109,5911611215606127268871,3550425722369343491079,18917190706623491883032,47288841538823033757752,3619075262433863928899,6056351323172805547141,10930903444683973731593,5911046587228858881031,3549863345796185852935,47261729271455890292753,18909101662154997661729,3619038636137084108817,245656461784339683754001,321140538534096742137873,642279906113066108993553,5911069128353250284551,3549883635116466506759,18917190152408889573400,76831887086116789067800,3619021835583322328131,6056369954053673780321,10930922075737648333921,19535101974058415161344,18909119658978517729297,5911051096328195019783,3549865603091411241991,94548804790602300473432,1200192430930340676689,19413336064,21630025728,10930885130668545680649,606271898307515634943009,94540734332373463810129,1218639192845604422753]),
(10,[1188,3392,1317,1286,1320],31966,[3549850949885973562435,5911043207324733805575,3549857714087950027783,5911051096328195019783,3549865603091411241991,47288246473758429414665,5911101811350391755783,3550062828177731881991,18917226216424707473432,47288345658597937553464,5911034330061187585031,3549990700148178553863,18917141823478369894424,47288234208710646341688,81687953141717804258437,5911051096328195019783,3549865603091411241991,303717588763899513275657,1200191286295727702016,303783001025383089571617,6056319344447254959237,5911046587228858881031,3549863345796185852935,47261729271455890292753,18909101662154997661729,94540734332442250330129,170024811082130522128401,866696637664198656,5911069128353250284551,3549883635116466506759,18917190152408889573400,170208152665729932501016,245839920593651416318128,6056332868474636342405,1218639192708031580033,18909119658978517729297,5911101811350391755783,3550062828177731881991,18917226216424707473432,47288345658597937553464,3619020602960892657664,6056374567471424738437,643165045572279357408801,18909155758195870810129,170208342019405036798128,5911322703754998846471,3550137210518215068679,18917425695512014635032,47288301969984377102392,77108832859107993324611,6056370200721227781253,94835577981228845368353,18909678123182447411217,170208414710387095781552,10930859210232213586480]),
(10,[1188,3392,1317,3398,1319],31198,[3549850949885973562435,5911043207324733805575,3549857714087950027783,5911051096328195019783,3549865603091411241991,47288246473758429217873,5911101811354623808519,3549848764258853063687,18917139498968026202136,47288231884391313350712,5911641783127408382983,3549990700146163190791,18917298344456276164632,47288841661583023185976,3619633831522893564995,5911322703446802437127,3550137210210018659335,18917425695527868055576,47288238857476020150328,3619031027708804992067,643016615345984808452768,5911046587228858881031,3549863345796185852935,47261729271455890292753,18909101662154997661729,3619038636137084108817,170172385034720198541329,321140538534096742137873,5911069128353250284551,3549883635116466506759,18917190152408889573400,76831887086116789067800,3619021835583322328131,170798476669178575127649,10930922075754307060833,18909119658978517729297,5911051096328195019783,3549865603091411241991,94548804790602300473432,1200192430930340676689,19413336064,606420030829638363645473,10930885130668545680649,94540734332373463810129,1218639192708568122465,5911246067794542859271,3549990700593813916679,18917298344456276164632,47288445962027150647352,3619168310804387728451,6056296663699767164928,10931003466157240886537,18909678123044874240017,76850451618784524436577,57314612023452488959009]),
(10,[1188,3392,1317,3398,1447],23518,[3549850949885973562435,5911043207324733805575,3549857714087950027783,5911051096328195019783,3549865603091411241991,47288246473758429217873,5911101811354623808519,3549848764258853063687,18917139498968026202136,47288231884391313350712,5911051234881837208583,3549990700164300409863,18917158728469646950424,47288373833610134946833,3619043283827615075395,5911322703446802437127,3550137210210018659335,18917425695527868055576,47288238857837721198648,3619031027708804992067,23782475221796290318484,5911611215606127268871,3550425722369343491079,18917190706623491883032,47288841538823033757752,3619075262433863928899,23782519456536362766484,10930903444683973731593,5911046587228858881031,3549863345796185852935,47261729271455890292753,18909101662154997661729,3619038636137084108817,170024811082130522128401,321140538534096742137873,642279906113066108993553,5911069128353250284551,3549883635116466506759,18917190152408889573400,76831887086116789067800,3619021835583322328131,23782538087315159516193,10930922075737648333921,19535101974058415161344,18909119658978517729297,5911051096328195019783,3549865603091411241991,94548804790602300473432,1200192430930340676689,3619168310272869796931,6056296663699767164928,10930885130668545680649,606271898307515634943009,94540734332373463810129,1218639192691909395553]),
(10,[1188,3392,1317,1414,3497],24030,[3549850949885973562435,5911043207324733805575,3549857714087950027783,5911051096328195019783,3549865603091411241991,47288246473758429414665,5911101811387942310919,3549883701240892754951,18917226216459033657368,47288266821415135649848,5911034330061187585031,3549990700148178553863,18917141823478369894424,47288234208710646341688,40253107187681283049570,5911322703446802437127,3550137210210018659335,18917425695527868055576,47288238857476020150328,40253111836416579504226,6056307088449896191109,5911051096328195019783,3549865603091411241991,303717588763899513275657,1200191286295727702016,606308775524575732041249,6056319344447254959237,10930885130668545680649,5911046587228858881031,3549863345796185852935,47261729271455890292753,18909101662154997661729,113374860031699702530065,170024811082130522128401,321140538534096742137873,866696637664198656,5911069128852524504071,3549883635615740726279,18917190152408923127832,245839803368488850464792,245839796658729939683410,6056332868973910561925,10931083236800627687664,76850362022948761634433,18909101662172194291729,5911069128336087192583,3549883635099303414791,18917190152408923127832,651751183337880956731952,3619024054364502278704,6056332868453174088837,10930885130668545680649,605682125460672245925409,18909101662172194291729,170208269891442254561840]),
(10,[1188,3392,1317,3399,1446],23518,[3549850949885973562435,5911043207324733805575,3549857714087950027783,5911051096328195019783,3549865603091411241991,47288246473758429217873,5911101811370745664519,3549865669250197228551,18917156404033346355224,47288301705578633298961,5911034330061187585031,3549990700148178553863,18917141823547156480024,47288234208896333422648,21345194512100040394834,5911322703446802437127,3550137210210018659335,18917425695527868055576,47288238857837721198648,21345199161055199119442,6056307088449896191109,5911611215606127268871,3550425722369343491079,18917190706623491883032,47288841538823033757752,21345243395799570729042,6056351323172805547141,10930903444683973731593,5911046587228858881031,3549863345796185852935,47261729271455890292753,18909101662154997661729,94466947356147412123665,245656461784339683754001,321140538534096742137873,642279906113066108993553,5911069128353250284551,3549883635116466506759,18917190152408889573400,76831887086116789067800,21345227124709964973089,6056369954053673780321,10930922075737648333921,19535101974058415161344,18909119658978517729297,5911051096328195019783,3549865603091411241991,170180455492811462164632,1200192430930340742289,3619020602960892657664,6056374567418760008837,10930885130668545680649,606271898307515634943009,170172385034582625501329,1218639192623122875553]),
(10,[1188,3392,1317,3399,1320],31198,[3549850949885973562435,5911043207324733805575,3549857714087950027783,5911051096328195019783,3549865603091411241991,47288246473758429283473,5911101811354623808519,3549848764258853063687,18917139499042069299224,47288231884433163067448,5911034330061187585031,3549990700148178553863,18917141823337824010264,47288234208827681054776,3619026378836203801667,5911322703447070872583,3550137210210287094791,18917425695512014635032,47288841802526871298104,3619633972395805510723,6056910033139046290565,5911046587228858881031,3549863345796185852935,47261729271455890292753,18909101662154997661729,94466947356147412123665,6056314696944745201681,321435686439276094963729,5911069128353250284551,3549883635116466506759,18917190152408889573400,152463537788325950693400,3619058991363637906499,6056297966759727600773,322061850201564113929377,18909119658978517729297,5911051096328195019783,3549865603091411241991,170180455492811462164632,1200192430930340742289,3619040959338582641731,21630025728,908799059826622956308001,170172385034582625501329,1218639193379775317153,5911322703754998846471,3550137210518215068679,18917425695512014635032,47288662345915496964152,3619310312766549527619,6056590951836474676357,10930848785177516179456,18909678123182447411217,152482246577056823510177,57314900535303617381409])]
set_option maxRecDepth 32000 in
set_option maxHeartbeats 0 in
theorem allTerms : reaches.all termPage=true := by decide +kernel
theorem allSigned (s : TerminalPage) (h : s∈reaches) : ∀ q, q≤s.1 → ¬Live true target q (termState s).toFinset :=
  terminal_sound (List.all_eq_true.mp allTerms s h)
end PEqualNP.Outside.L_meta_9822.Ranked

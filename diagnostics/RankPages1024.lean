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
def page0 : List Sample := [(11,[4129,1188,1252,1317,1286,1319],64847,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,1286,1320],64719,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1317,1286],32719,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1252,1317,326,1319,1480],112975,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1252,1317,326,1319,1485],112975,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1252,1317,326,1319,1518],112975,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,326,1319],63823,3,2,7,10,720583367873539204,720582834223368324,648545031783821444),
(10,[4129,1188,1252,1317,326,1320,1416],125135,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1252,1317,326,1320,1480],112847,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,326,1320],63951,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,326,1416],60367,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,326,1480],48079,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,326,1485],48079,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1317,326],31695,3,3,6,8,324286159260797192,19430785730087960,27312699419536672),
(11,[4129,1188,1252,1317,1446,1319],64847,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1317,1446],32719,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,1319,1478],64847,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,1319,1448],64847,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,1319,1480],64847,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1252,1317,1319,362,1512],96591,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1252,1317,1319,362,1518],96591,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,1319,362],63823,3,2,7,9,720583367873539204,720582834223368324,648545031783821444),
(10,[4129,1188,1252,1317,1319,394,1512],96591,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1252,1317,1319,394,1517],96591,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,1319,394],63823,3,3,5,6,324288358284052744,19430785727988760,29564499233221920),
(10,[4129,1188,1252,1317,1319,426,1512],96591,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,1319,426],63823,3,2,7,9,722835167687224452,722834634037053572,648545031783821444),
(11,[4129,1188,1252,1317,1319,428],64847,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1252,1317,1320,1416,426],125135,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1252,1317,1320,1416,458],125135,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,1320,1416],60623,3,3,7,9,19430785727988760,326539776919390472,299518087887203616),
(11,[4129,1188,1252,1317,1320,362],63951,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1252,1317,1320,394,1512],96463,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,1320,394],63951,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,1320,426],63951,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,1320,458],63951,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,1416,426],60367,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1317,1416],28623,3,3,6,9,326539776919390472,19430785727988760,29566697795104032),
(12,[4129,1188,1252,1317,1448],32719,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,362,1480],48079,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1317,362],31695,3,3,6,8,326540158097737992,21682518971780122,29564497083641122),
(11,[4129,1188,1252,1317,394,1480],48079,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1317,394,1485],48079,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1317,394],31695,3,3,6,8,324288358284052744,19430785727988760,29564499233221920),
(11,[4129,1188,1252,1317,426,1480],48079,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1317,426],31695,3,3,6,8,326537959074482440,19430785730087960,27312699419536672),
(12,[4129,1188,1252,1317,428],32719,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1286,1319],32623,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1286,1320],32495,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1286,1385],30703,2,0,4,0,180163507378143265,0,0),
(12,[4129,1188,1252,1286,1449],24559,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1286,427],24559,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1286,428],24559,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1318,1320,1416],60655,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1318,1320],32239,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1318,1416],28655,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1318,427],24559,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1318,428],24559,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,326,1319,1448],56175,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,326,1319,1485],56175,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1252,326,1320,1416,1449],116975,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,326,1320,1416],60143,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,326,1320,1448],56047,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,326,1320,1449],55791,2,1,2,0,148692184136360966,0,0)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page0_ok : page0.all (replay raw target)=true := by decide +kernel
def page1 : List Sample := [(11,[4129,1188,1252,326,1320,1485],39919,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,326,1320],31727,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,326,1416,1449],52207,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,326,1448,1385],54255,2,0,4,0,180163507378143265,0,0),
(12,[4129,1188,1252,1319,1446],32623,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1319,1448],32623,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1319,362,1480],47983,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1319,362,1485],47983,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1319,394,1480],47983,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1320,1416,426],60143,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1320,362,1485],39919,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1320,362],31727,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1320,394,1480],47855,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1252,1320,394,1485],39919,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1320,394],31727,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1320,426],31727,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1320,427],24559,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1252,1320,428],24559,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,1254,1319],64847,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,1254,1320],64719,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1317,1254],32719,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1284,1317,326,1319,1479],112975,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,326,1319],63951,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1284,1317,326,1479,1320],112847,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,326,1479],48079,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1284,1317,326,1320,1485],112847,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1284,1317,326,1320,1518],112847,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,326,1485],48079,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,1382,1319],62927,2,0,8,0,27058097889587217,0,0),
(11,[4129,1188,1284,1317,1382,1320],62671,3,0,7,8,27058097889587217,180162893197819937,37181515284690208),
(11,[4129,1188,1284,1317,1446,1320],64719,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1317,1446],32719,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,1319,362],63951,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,1319,394],63951,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,1319,426],63951,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1317,1319],32207,3,4,6,10,326583764900694336,722900532109389376,720928213718745376),
(10,[4129,1188,1284,1317,327,1320,1485],112847,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1284,1317,327,1320,1518],112847,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,327,1481],47567,3,4,6,9,324331965087009088,324611241040695872,720928215866229024),
(11,[4129,1188,1284,1317,327,1485],48079,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,1447,1320],64719,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1317,1447],32719,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,1320,1478],64719,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1284,1317,1320,1479,458],112847,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,1320,1479],64719,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1284,1317,1320,362,1511],96463,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1284,1317,1320,362,1518],96463,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1284,1317,1320,394,1511],96463,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1284,1317,1320,394,1517],96463,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1284,1317,1320,426,1511],96463,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1284,1317,1320,458,1511],96463,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1284,1317,1320,458,459],112847,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,1320,459],64719,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,1320,428],64719,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,362,1479],48079,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,394,1479],48079,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,394,1485],48079,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1317,426,1479],48079,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1317,428],32719,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1254,1318,1320],64687,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1254,1318],32687,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1254,1319],32623,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1254,1320],32495,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1254,1449],24559,2,1,2,0,148692184136360966,0,0)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page1_ok : page1.all (replay raw target)=true := by decide +kernel
def page2 : List Sample := [(12,[4129,1188,1284,1254,427],24559,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1254,428],24559,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1318,1320],31983,3,4,6,11,148936044472193184,720751987213418784,326689318016961152),
(12,[4129,1188,1284,1318,427],24559,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1318,428],24559,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,326,1319,1447],56175,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,326,1319,1485],39919,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,326,1319],31727,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,326,1447,1320],56047,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,326,1447,459],39919,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,326,1320,1449],55535,3,4,6,9,148936044474290336,720751987215515936,324435319180020352),
(11,[4129,1188,1284,326,1320,1485],56047,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1382,1319],30703,2,0,4,0,180162893197819937,0,0),
(12,[4129,1188,1284,1382,1320],30447,3,0,4,9,180162893197819937,27058097889587217,27058479067903264),
(11,[4129,1188,1284,1319,362,1485],39919,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1319,362],31727,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1319,394,1485],39919,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1319,394],31727,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1319,427],24559,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1319,428],24559,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,327,1320,1485],56047,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1320,1446],32495,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1320,1447,426],56047,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1320,1447],32495,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1320,362,1479],47855,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1320,362,1485],47855,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1320,394,1479],47855,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1320,426,1479],47855,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1284,1320,426,427],56047,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1284,1320,427],32495,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1254,1414,1319],64799,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1254,1414],32671,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1254,1287,1320],64607,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1254,1287,1481],48479,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1254,1287],32607,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1254,1319,1451],62815,2,0,4,0,27058295458082833,0,0),
(11,[4129,1188,1317,1254,1320,1448],56543,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1254,1320,1451],54751,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1317,1254,1320],32223,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1254,1448,460],36831,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1254,1448],24543,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1254,427],24543,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1254,1451],30687,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1317,1254,428],24543,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1254,1452],24543,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1286,1319],32223,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1286,1383,1320],62687,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1317,1286,1383],30687,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1317,1286,427],24543,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1286,428],24543,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1286,1452],24543,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,326,1287,1447,1320],120927,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,326,1287,1447,1481],104799,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,326,1287,1447],56159,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,326,1287,1320,1451],119007,2,0,4,0,27058097891684369,0,0),
(10,[4129,1188,1317,326,1287,1320,1485],104671,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,326,1287,1320],63711,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,326,1287,1481,1451],102879,2,0,4,0,27058097891684369,0,0),
(11,[4129,1188,1317,326,1287,1481],47583,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,326,1287,1451],54239,2,0,4,0,27058097891684369,0,0),
(11,[4129,1188,1317,326,1287,460],43999,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,326,1287,1485,492],68575,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,326,1287,1485],39903,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,326,1287],31711,2,1,2,0,148692184136360966,0,0)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page2_ok : page2.all (replay raw target)=true := by decide +kernel
def page3 : List Sample := [(10,[4129,1188,1317,326,1319,1447,1515],119135,2,0,4,0,27058297607663633,0,0),
(11,[4129,1188,1317,326,1319,1448],55775,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,326,1319,1451],53727,3,0,4,8,27058097891684369,720594848482279457,37181517432174096),
(11,[4129,1188,1317,326,1319,1452],55775,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,326,1319,1485],55775,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,326,1383],31711,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,326,1383,1320,1448],119007,2,0,4,0,27058297607663633,0,0),
(11,[4129,1188,1317,326,1383,1320],61919,2,0,4,0,27058297607663633,0,0),
(11,[4129,1188,1317,326,1383,1448],54239,2,0,4,0,27058297607663633,0,0),
(11,[4129,1188,1317,326,1383,1452],54239,2,0,4,0,27058297607663633,0,0),
(11,[4129,1188,1317,326,1415,1451],54239,2,0,4,0,27058097891684369,0,0),
(11,[4129,1188,1317,326,1415,1485],39903,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,326,1415],31711,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,326,1447,1320],55775,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,326,1447,459],39903,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,326,1447,1483],54239,2,0,4,0,27058297607663633,0,0),
(11,[4129,1188,1317,326,1447,460],39903,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,326,1320,1451],53727,3,0,4,8,27058097891684369,180162893197819937,37181517432174096),
(11,[4129,1188,1317,326,1320,1452],55775,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,326,1320,1485],55775,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,326,1384],31711,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,326,1416,1451,494],70623,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,1317,326,1416,1451],54239,2,0,4,0,27058097891684369,0,0),
(11,[4129,1188,1317,326,1416,1452],52191,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,326,1416,1485],39903,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,326,1416],31711,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1382,1319],32223,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1382,1320,461],40415,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1382,1320],32223,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1382,1287,1320],62687,2,0,4,0,27058097889587217,0,0),
(11,[4129,1188,1317,1382,1287,1481],46559,2,0,4,0,27058097889587217,0,0),
(12,[4129,1188,1317,1382,1287],30687,2,0,4,0,27058097889587217,0,0),
(11,[4129,1188,1317,1382,1319,461],46559,2,0,4,0,27058097889587217,0,0),
(12,[4129,1188,1317,1382,1319],30175,3,0,4,9,27058097889587217,720594848482279457,37181515284690448),
(12,[4129,1188,1317,1382,1415],30687,2,0,4,0,27058097889587217,0,0),
(11,[4129,1188,1317,1382,1320,461],46559,2,0,4,0,27058097889587217,0,0),
(12,[4129,1188,1317,1382,1320],30175,3,0,4,9,27058097889587217,180162893197819937,37181515284690448),
(11,[4129,1188,1317,1382,1416,461],38879,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1317,1382,1416],30687,2,0,4,0,27058097889587217,0,0),
(12,[4129,1188,1317,1414,1319],32223,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1414,1383],30687,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1317,1414,1320],32223,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1414,1416],28639,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,1287,1444,1320,426],121039,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,1444,1320],64719,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,1444,1449],56783,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,1287,1444,426,1513],88527,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,1444,426],56271,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,1444,428],53199,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1287,1444],32719,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,1320,362],63711,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,1320,394],63711,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,1287,1320,426,1508],96463,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,1320,426],63711,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,1320,458],63711,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1287,1416],32479,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,1287,1449,426,1508],88527,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,1449,426],55775,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1287,1449],32223,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,1449,362],55775,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,1449,394],55775,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,1449,458],55775,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1287,1449],24031,3,5,7,10,299562167136562496,722900532109389376,723120640365833504),
(11,[4129,1188,1317,1287,362,428],52191,2,1,2,0,148692184136360966,0,0)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page3_ok : page3.all (replay raw target)=true := by decide +kernel
def page4 : List Sample := [(11,[4129,1188,1317,1287,362,1485],39903,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1287,362],31711,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,394,1480],47839,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,394,428],52191,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,394,1485],39903,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1287,394],31711,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,1287,426,1476,428],101327,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,426,1476],48079,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,426,1481],47583,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,426,428],52191,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1287,426],31711,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,427,1481],40415,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1287,427],24543,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1287,428],28639,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1287,428],24543,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,1287,428,1472,1476],102350,2,0,1,0,148692183061570566,0,0),
(9,[4129,1188,1317,1287,428,1472,458,1540],166862,2,0,1,0,148692183061570566,0,0),
(9,[4129,1188,1317,1287,428,1472,458,491],197598,2,0,1,0,148692183061569542,0,0),
(10,[4129,1188,1317,1287,428,1472,458],101342,2,0,1,0,148692183061570566,0,0),
(10,[4129,1188,1317,1287,428,1472,491],83934,2,0,1,0,148692183061569542,0,0),
(11,[4129,1188,1317,1287,428,1472],53214,2,0,1,0,148692183061570566,0,0),
(11,[4129,1188,1317,1287,428,1476],53199,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,1287,428,458,1504],84958,2,0,1,0,148692184135312390,0,0),
(10,[4129,1188,1317,1287,428,458,1508],84943,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1287,428,458],52191,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1287,1452],24543,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1319,1446],32223,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1319,1384],32223,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1319,1416],32223,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1319,1448],32223,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1319,362,1480],47583,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1319,362,1485],47583,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1319,362],31199,3,5,7,9,326583764900694336,720648732295704128,720866641528892704),
(11,[4129,1188,1317,1319,394,1480],47583,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1319,1451],32223,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,327,1444,1416],56271,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,327,1320,1448,1508],121039,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,327,1320,1451],53727,3,0,4,8,27058295460179985,180163090766315553,180170805601314320),
(11,[4129,1188,1317,327,1320,1452],55775,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,327,1320,1485],55775,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,327,1320,1485],39391,3,5,7,9,297871118253436224,594827218682925632,720928216327595296),
(11,[4129,1188,1317,327,1384,1449],55775,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,327,1384],31711,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,327,1416,1448],56031,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,327,1416,1449],55775,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,327,1416,1451,494],70623,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,1317,327,1416,1451],54239,2,0,4,0,27058295460179985,0,0),
(11,[4129,1188,1317,327,1416,1485],39903,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,327,1416],31711,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,327,1448,1476,1481],104911,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,327,1448,1476],56271,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,327,1448,1481],55775,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,1317,327,1448,459,1513],72159,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,327,1448,459],39903,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,327,1448,460],39903,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1383,1320,362],61919,2,0,4,0,27058297607663635,0,0),
(12,[4129,1188,1317,1383,1320],32223,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1383,362,1480],46047,2,0,4,0,27058297607663633,0,0),
(12,[4129,1188,1317,1383,394],31711,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1383,1320,394],61919,2,0,4,0,27058297607663633,0,0),
(11,[4129,1188,1317,1383,1320,426],61919,2,0,4,0,27058295458082833,0,0),
(11,[4129,1188,1317,1383,1320,458],61919,2,0,4,0,27058297607663633,0,0),
(12,[4129,1188,1317,1383,1320],30175,3,0,4,9,27058295458082833,180163090766315553,182424802290707984),
(11,[4129,1188,1317,1383,1416,461],38879,2,0,4,0,27058712069910545,0,0)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page4_ok : page4.all (replay raw target)=true := by decide +kernel
def page5 : List Sample := [(12,[4129,1188,1317,1383,1416],30687,2,0,4,0,27058295458082833,0,0),
(11,[4129,1188,1317,1383,394,1480],46047,2,0,4,0,27058297607663633,0,0),
(11,[4129,1188,1317,1383,426,1480],46047,2,0,4,0,27058297607663633,0,0),
(11,[4129,1188,1317,1383,426,1484],46047,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1317,1415,1320],32223,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1415,362],31711,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1415,394],31711,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1415,426],31711,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1320,1446],32223,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1320,1447,426],55775,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1320,1447],32223,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1320,362,1479],47583,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1320,362,1485],47583,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1320,394,1479],47583,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1320,426,1479],47583,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1320,426,427],55775,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1320,427],32223,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1320,1451],32223,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1384,394,1474],48091,2,1,4,0,360295395332739138,0,0),
(12,[4129,1188,1317,1384,394],31711,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1416,362],31711,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,1416,394,1474],48091,2,1,4,0,360295395332739138,0,0),
(12,[4129,1188,1317,1416,394],31711,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1317,1416,426],31711,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,362,1447,1484],39903,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,362,1448,1484],39903,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,394,1447,459],39903,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1317,394,1448,459],39903,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1254,1318,1287,1320],64575,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1254,1318,1287],32575,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1254,1318,1320],32191,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1254,1318,1384],30655,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1318,395],30655,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1318,1419],30655,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1254,1318,1451],30655,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1287,1444],32623,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1254,1287,1320],32383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1254,1287,1385],30591,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1287,1449],24447,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1254,1287,395],30591,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1287,1419],30591,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1254,1287,427],30591,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1287,1451],30591,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1319,1384],30591,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1319,395],30591,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1319,1419],30591,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1254,1319,1451],30591,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1320,1416],28415,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1254,1320,395,1480],42751,2,0,4,0,27058712069910545,0,0),
(11,[4129,1188,1254,1320,395,461],34815,2,0,4,0,27058712069910545,0,0),
(11,[4129,1188,1254,1320,395,1485],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1320,395],26623,2,0,4,0,27058712069910545,0,0),
(11,[4129,1188,1254,1320,1419,461],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1320,1419],26623,2,0,4,0,27058295458082833,0,0),
(11,[4129,1188,1254,1320,427,1479],38783,2,0,4,0,27058712069910545,0,0),
(11,[4129,1188,1254,1320,427,1484],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1320,427],22527,2,0,4,0,27058712069910545,0,0),
(11,[4129,1188,1254,1320,1451,460],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1320,1451],22527,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1320,428],20479,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1254,1320,1452,459],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1320,1452],20479,2,1,2,0,148692184136360966,0,0),
(13,[4129,1188,1254,1320],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1254,1384,395],26623,2,0,4,0,27058712069910545,0,0)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page5_ok : page5.all (replay raw target)=true := by decide +kernel
def page6 : List Sample := [(12,[4129,1188,1254,1384,428],20479,2,1,2,0,148692184136360966,0,0),
(13,[4129,1188,1254,1384],16383,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1254,1384,1417,461],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1384,1417],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1384,428],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1384,428],22527,2,0,4,0,27058712069910545,0,0),
(11,[4129,1188,1254,1384,428,1481],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1384,1452],22527,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1416,395],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1416,1419],26623,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1254,1416,427],22527,2,0,4,0,27058712069910545,0,0),
(13,[4129,1188,1254,1416],16383,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1254,1416,1385,461],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1416,1385],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1416,427],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1416,427],20479,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1254,1416,427,1481],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1416,1451],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1385,395],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1385,428],20479,2,1,2,0,148692184136360966,0,0),
(13,[4129,1188,1254,1385],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1254,1385,428],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1385,428],22527,2,0,4,0,27058712069910545,0,0),
(11,[4129,1188,1254,1385,428,1480],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1385,1452],22527,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1417,395],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1417,1419],26623,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1254,1417,427],22527,2,0,4,0,27058712069910545,0,0),
(13,[4129,1188,1254,1417],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1254,1417,427],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1417,427],20479,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1254,1417,427,1480],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,1417,1451],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,395,1419],26623,2,0,4,0,27058295458082833,0,0),
(13,[4129,1188,1254,395],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1254,395,1448],22527,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,395,1449],22527,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,395,1448],20479,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1254,395,1449],20479,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1254,395,1448],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1254,395,1449],26623,2,0,4,0,27058712069910545,0,0),
(13,[4129,1188,1254,1419],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1254,1419,425],30207,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1286,1319,1419],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1286,1319,1451],22527,2,0,4,0,27058712069910545,0,0),
(13,[4129,1188,1286,1319],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1286,1383,395],26623,2,0,4,0,27058295458082833,0,0),
(13,[4129,1188,1286,1383],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1286,1383,1320],30463,2,0,4,0,27058295458082833,0,0),
(11,[4129,1188,1286,1383,1417,461],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1286,1383,1417],26623,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1286,1383,428],26623,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1286,1383,1452],22527,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1286,1415,1419],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1286,1415,427],22527,2,0,4,0,27058712069910545,0,0),
(13,[4129,1188,1286,1415],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1286,1320,1419],30463,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1286,1320,427],30463,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1286,1320,1451],30463,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1286,1385,395],26623,2,0,4,0,27058712069910545,0,0),
(13,[4129,1188,1286,1385],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1286,1385,428],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1286,1385,1452],22527,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1286,1417,1419],26623,2,0,4,0,27058712069910545,0,0)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page6_ok : page6.all (replay raw target)=true := by decide +kernel
def page7 : List Sample := [(12,[4129,1188,1286,1417,427],22527,2,0,4,0,27058712069910545,0,0),
(13,[4129,1188,1286,1417],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1286,1417,427],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1286,1417,427],20479,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1286,1417,427,1479],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1286,1417,1451],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1286,395,1447],20479,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1286,395,1449],20479,2,1,2,0,148692184136360966,0,0),
(13,[4129,1188,1286,1419],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1318,1287,1320],31999,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,1318,1287,1419,461],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1318,1287,1419],26623,2,0,4,0,27058712069910545,0,0),
(11,[4129,1188,1318,1287,427,1478],38847,2,0,4,0,27058712069910545,0,0),
(11,[4129,1188,1318,1287,427,1484],34815,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1318,1287,427],22527,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1318,1287,1451],22527,2,0,4,0,27058712069910545,0,0),
(13,[4129,1188,1318,1287],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1318,1383,395],26623,2,0,4,0,27058295458082833,0,0),
(13,[4129,1188,1318,1383],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1318,1383,1320],30207,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1318,1383,428],26623,2,0,4,0,27058295458082833,0,0),
(12,[4129,1188,1318,1383,1452],22527,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1318,1415,1419],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1318,1415,427],22527,2,0,4,0,27058712069910545,0,0),
(13,[4129,1188,1318,1415],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1318,1320,1419],30207,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1318,1320,427],30207,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1318,1320,1451],30207,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1318,1384,395],26623,2,0,4,0,27058712069910545,0,0),
(13,[4129,1188,1318,1384],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1318,1384,428],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1318,1384,1452],22527,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1318,1416,1419],26623,2,0,4,0,27058712069910545,0,0),
(12,[4129,1188,1318,1416,427],22527,2,0,4,0,27058712069910545,0,0),
(13,[4129,1188,1318,1416],16383,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1318,395,1447],20479,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,1318,395,1448],20479,2,1,2,0,148692184136360966,0,0),
(13,[4129,1188,1318,1419],16383,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,326,1287,1444,1415],60271,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,326,1287,1444,1452],52207,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,326,1287,1444],31727,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,326,1287,1415,1320],60031,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,326,1287,1415,1385],58239,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,1415,1449],52095,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,326,1287,1415,427],58239,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,1415,1451],58239,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,1415,459],58239,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,1415,1483],58239,2,0,4,0,27058297607663633,0,0),
(11,[4129,1188,326,1287,1320,1417],59647,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,326,1287,1320,1419],58111,2,0,4,0,27058097891684369,0,0),
(11,[4129,1188,326,1287,1320,1452],51967,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,326,1287,1320],31487,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,326,1287,1385,1452,494],66559,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,1385,1452],50175,2,0,4,0,27058712072007697,0,0),
(10,[4129,1188,326,1287,1385,461,1516],66559,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,1385,461],37887,2,0,4,0,27058712072007697,0,0),
(12,[4129,1188,326,1287,1385],29695,2,0,4,0,27058712072007697,0,0),
(10,[4129,1188,326,1287,1417,427,1518],66559,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,1417,427],50175,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,1417,1451],50175,2,0,4,0,27058712072007697,0,0),
(10,[4129,1188,326,1287,1417,1485,491],66559,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,1417,1485],35839,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,326,1287,1417],27647,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,326,1287,1449,1419,494],66559,2,0,4,0,27058712072007697,0,0)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page7_ok : page7.all (replay raw target)=true := by decide +kernel
def page8 : List Sample := [(11,[4129,1188,326,1287,1449,1419],50175,2,0,4,0,27058097891684369,0,0),
(10,[4129,1188,326,1287,1449,459,1516],66559,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,1449,459],37887,2,0,4,0,27058712072007697,0,0),
(12,[4129,1188,326,1287,1449],23551,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,326,1287,1419,461],41983,2,0,4,0,27058712072007697,0,0),
(10,[4129,1188,326,1287,1419,461,1513],66559,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,427,1452],50175,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,427,1484],41983,2,0,4,0,27058712072007697,0,0),
(12,[4129,1188,326,1287,427],29695,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,427,1484],35839,2,1,2,0,148692184136360966,0,0),
(12,[4129,1188,326,1287,427],23551,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,326,1287,427,1481],37887,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,427,1484],50175,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,1451,1452],50175,2,0,4,0,27058712072007697,0,0),
(12,[4129,1188,326,1287,1451],29695,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,1452,459],41983,2,0,4,0,27058712072007697,0,0),
(12,[4129,1188,326,1287,1452],27647,2,1,2,0,148692184136360966,0,0),
(11,[4129,1188,326,1287,1452,459],50175,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,1452,459],35839,2,1,2,0,148692184136360966,0,0),
(10,[4129,1188,326,1287,1452,459,1513],66559,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1287,1452,1483],50175,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1319,1415,1384],58239,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1319,1415,1451],58239,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1319,1415,459],58239,2,0,4,0,27058712072007697,0,0),
(11,[4129,1188,326,1319,1415,1483],58239,2,0,4,0,27058297607663633,0,0),
(12,[4129,1220,1317,1320,1384],29951,3,3,4,10,19430785727988760,596755754561620232,360314483833386512),
(12,[4129,1220,1318,1320,1444],32175,3,1,8,9,594482575956259906,594482179745271874,720595064530011202),
(12,[4129,1220,1318,1320,1384],31935,3,5,6,10,148655669006906528,360324379438036256,326689318016961152),
(12,[4129,1252,1317,1412,1319],32111,3,2,8,11,596734378118753412,596733844468582532,648545031783821444),
(12,[4129,1252,1317,1381,1319],32095,3,5,6,9,326583764900694336,182468576824929856,182688685081373984),
(11,[4129,1252,1317,1319,362,1477],47455,3,5,6,8,324331965087009088,722900532109389376,723118441342577952),
(11,[4129,1252,1317,1319,394,1476],47471,3,2,7,9,722835167687224452,722834634037053572,648545031783821444),
(12,[4129,1252,1317,1320,1384],29951,3,3,4,10,19430785727988760,596755754561620232,299518087887203856),
(12,[4129,1252,1318,1320,1384],29951,3,3,4,10,19430785727988760,326539776919390472,299518186671451664),
(11,[4129,1252,326,1320,1384,1417],57599,3,3,4,8,19430785730087960,324285778082449672,297264187834510864),
(12,[4129,1284,1221,1320,1417],27903,3,5,7,10,148655668805579936,648554755589748000,596905295659190912),
(11,[4129,1284,1317,326,1320,1451],53503,3,3,4,9,19430785730087960,594501755724679432,360314483833386512),
(11,[4129,1284,1317,326,1320,1452],51455,3,5,7,9,148655668805579936,648554755589748000,594651296822250112),
(11,[4129,1284,1317,327,1320,1451],53503,3,3,4,9,19430785730087960,594501755724679432,360314483833513488),
(11,[4129,1221,1285,1254,1287,1417],60959,3,0,7,10,324278695454068769,324278081273675809,299562159620369441),
(12,[4129,1221,1285,1254,1319],32543,3,1,2,10,148692184136360966,720583132520657986,74316821343291524),
(12,[4129,1221,1285,1287,1446],32415,3,0,8,9,324278695454068769,324278081273675809,299562159620369441),
(12,[4129,1221,1285,1287,1383],32351,3,3,9,10,180170590006755592,182424970021882120,148655668805579936),
(11,[4129,1221,1317,1254,1287,1320],64543,3,0,4,7,27058712069910545,180162893197819937,37181515512231440),
(11,[4129,1221,1317,1254,1287,1481],48415,3,0,4,8,27058712069910545,720594848482279457,37181515512231440),
(12,[4129,1221,1317,1254,1287],32543,3,1,2,10,148692184136360966,148625979844350018,74316821343291524),
(11,[4129,1221,1317,1254,1320,1448],56479,3,0,4,8,27058712069910545,180162893197819937,37181515512231440),
(12,[4129,1221,1317,1254,1320],32159,3,0,4,9,27058712069910545,180162893197819937,37181515512231440),
(12,[4129,1221,1317,1286,1319],32159,3,0,4,9,27058712069910545,720594848482279457,37181515512231440),
(11,[4129,1221,1317,1287,1383,1320],62559,3,0,4,7,27058712069910545,180163090766315553,37181515512231440),
(12,[4129,1221,1317,1287,1320],31967,3,0,4,9,27058712069910545,180162893197819937,37181515512231440),
(12,[4129,1221,1317,1287,1449],24031,3,0,4,10,27058712069910545,720594848482279457,37181515512231440),
(12,[4129,1221,1317,1383,1320],30175,3,0,4,9,27058712069910545,180163090766315553,37181515512231440),
(11,[4129,1221,1254,1287,1320,1385],62527,3,1,2,7,148692184136360966,148626212846325826,74316821343291524),
(12,[4129,1221,1254,1287,1320],32319,3,1,2,9,148692184136360966,148625979844350018,74316821343291524),
(12,[4129,1221,1254,1287,1385],30527,3,1,2,9,148692184136360966,148626212846325826,74316821343291524),
(12,[4129,1221,1254,1287,1449],24383,3,1,2,10,148692184136360966,148625979844350018,74316821343291524),
(12,[4129,1221,1286,1320,1445],32415,3,1,8,9,324266598313775170,297244767547831362,299528453789068354),
(12,[4129,1221,1286,1320,1385],31935,3,3,4,10,19431166906336280,596755754561620232,360314582617634320),
(12,[4129,1221,1287,1320,1385],29951,3,3,4,10,19431166906336280,596755754561620232,648544958769346064),
(12,[4129,1253,1317,1286,1320],31967,3,0,4,9,27058712069910545,180163090766315553,182424802518248976),
(10,[4129,1253,1317,326,1287,1320,1451],118879,3,0,4,6,27058712072007697,180163092913799201,37181517659715088),
(11,[4129,1253,1317,326,1287,1320],63583,3,0,4,7,27058712072007697,180163092913799201,180170805828791824),
(11,[4129,1253,1317,326,1320,1448],55519,3,0,4,8,27058712072007697,180163092913799201,180170805828791824)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page8_ok : page8.all (replay raw target)=true := by decide +kernel
def page9 : List Sample := [(11,[4129,1253,1317,326,1320,1451],53727,3,0,4,8,27058712072007697,180163092913799201,37181517659715088),
(12,[4129,1253,1317,326,1320],31199,3,0,4,9,27058712072007697,180163092913799201,180170805828791824),
(11,[4129,1253,1317,1287,1320,394],63583,3,0,4,7,27058712072007697,596746058443671587,182422605640379922),
(11,[4129,1253,1317,1287,1320,426],63583,3,0,4,7,27058712072007697,180163092913799201,182422605642477072),
(11,[4129,1253,1317,1287,1320,458],63583,3,0,4,7,27058712072007697,180163092913799201,180170803681308176),
(12,[4129,1253,1317,1287,1416],32351,3,2,8,10,39413924231654532,182402979398207620,299528455938649220),
(12,[4129,1253,1317,1287,1449],32095,3,0,4,9,27058712069910545,648537452012847137,182424802518248976),
(11,[4129,1253,1317,1287,394,1480],47711,3,2,7,9,39413924233751684,182402979400304772,297274457101710468),
(11,[4129,1253,1317,1287,426,1481],47455,3,0,4,8,27058712072007697,648537454160330785,182422603494993424),
(12,[4129,1253,1317,1320,394],31199,3,0,4,9,27058712072007697,596746058443671587,182422605640379922),
(12,[4129,1253,1317,1320,426],31199,3,0,4,9,27058712072007697,180163092913799201,180170803681308176),
(12,[4129,1253,1318,1287,1320],31871,3,3,4,11,19431166906336280,648544951253192968,648544958769346064),
(11,[4129,1253,326,1287,1320,1417],59519,3,3,4,9,19431166908435480,648544951253192968,648544958769346064),
(12,[4129,1285,1254,1318,1287],32319,3,1,2,9,148692184136360966,148626212846325826,74316821343775876),
(11,[4129,1285,326,1413,1287,1447],59999,3,3,7,9,180170590006755592,180170971184941320,148655668805579936),
(12,[4129,1317,1254,1413,1319],32095,3,0,4,8,27058712069910545,594494256484401185,37181515512231440),
(12,[4129,1317,1254,1382,1319],32063,3,1,2,9,148692184136360966,648525771484705858,74316821343291524),
(12,[4129,1317,1254,1287,1320],31871,3,3,4,11,19431166906336280,596755754561620232,648544859985130000),
(12,[4129,1317,1254,1320,1416],27903,3,3,4,10,19431166906336280,596755754561620232,360314483833386512),
(11,[4129,1317,326,1413,1287,1320],59615,3,0,4,7,27058712072007697,180162893197819937,37181517659715088),
(11,[4129,1317,326,1413,1287,1481],43487,3,0,4,8,27058712072007697,720594848482279457,37181517659715088),
(11,[4129,1317,326,1287,1415,1320],59519,3,3,4,10,19431166908435480,594501755724679432,648544859985130000),
(11,[4129,1317,326,1287,1320,1419],57599,3,3,4,9,19431166908435480,594501755724679432,648544958769346064),
(11,[4129,1317,326,1287,1320,1452],51455,3,3,4,9,19431166908435480,594501755724679432,360314483833386512),
(12,[4129,1317,326,1287,1320],30975,3,3,4,11,19431166908435480,594501755724679432,648544859985130000),
(11,[4129,1317,326,1319,1415,1477],59743,3,0,4,7,27058712072007697,594494258631884833,37181517659715088),
(12,[4129,1317,1287,1320,362],30975,3,3,4,10,19431166908435480,596753555538364680,648544859985130000),
(12,[4129,1317,1287,1320,394],30975,3,3,4,10,19431166908433432,594501755724679432,648544859985130000),
(12,[4129,1317,1287,1320,426],30975,3,3,4,10,19431166908433432,596753488964274442,299515817994890770),
(12,[4129,1254,1318,1320,1447],32063,3,1,2,8,148692184136360966,148626212846325826,74316821343775876),
(12,[4129,1254,1318,1320,1384],31935,3,3,4,10,19431166906336280,594501755724747016,360314582617634320),
(12,[4228,1185,1287,1320,394],27391,3,0,4,5,27058712072007697,342293091816196129,180170805601250608),
(12,[4228,1217,1253,1317,394],27615,3,0,4,10,27058712072007697,198177491423281185,180170805828791600),
(12,[4228,1217,1287,1320,394],27391,3,0,4,5,27058712072007697,198177905887625249,37181517432173872),
(12,[4228,1281,1253,1317,394],27615,3,0,4,10,27058712072007697,198177491423281185,180170805828791600),
(12,[4228,1282,1221,1317,394],27615,3,0,4,10,27058712072007697,198177291707301921,37181517659714864),
(12,[4228,1221,1378,1317,362],29663,3,0,4,10,27058712072007697,198177291707301921,37181382368245040),
(12,[4228,1221,1285,1254,1287],32351,3,3,9,11,342300176592093448,342300557770279176,148655668798240008),
(11,[4228,1221,1285,1254,1287,1417],60959,3,0,7,10,342293093963550753,342292479783157793,297310359806684193),
(10,[4228,1221,1285,1254,1287,362,1507],96791,3,1,2,7,148692184136352774,148625971238686786,92331219854870660),
(11,[4228,1221,1285,1254,1287,362],64031,3,1,2,8,148692184136360966,148625979837009986,92331219854870660),
(11,[4228,1221,1285,1254,1287,426],64031,3,0,6,7,324278695454068769,324278081273675809,297310359806684193),
(12,[4228,1221,1285,1254,1319],32543,3,1,2,10,148692184136360966,720583132513317954,92348812025186436),
(12,[4228,1221,1285,1287,1446],32415,3,0,8,9,342293093963550753,342292479783157793,297310359806684193),
(11,[4228,1221,1285,1287,362,1479],47711,3,3,8,9,342300176592093448,342300557770279176,148655668805579936),
(11,[4228,1221,1285,1319,327,1478],47903,3,0,4,7,27058712072007697,324278695454068769,74336214358043824),
(12,[4228,1221,1285,1319,327],31583,3,0,4,8,27058712072007697,324278695454068769,324278297095965872),
(11,[4228,1221,1285,327,1448,1478],55967,3,0,7,8,324278695454068769,198177291707301921,297310359806684193),
(11,[4228,1221,1285,1385,362,1475],46039,3,0,3,10,27058712071999505,27041120038996001,297256699323354136),
(12,[4228,1221,1285,1385,362],29663,3,3,4,7,19431166908435480,342300557770279176,324285686814454064),
(11,[4228,1221,1317,1410,423,362],54111,3,0,4,8,27058711939887121,342292346639239201,37181382368245040),
(12,[4228,1221,1317,1410,362],29663,3,0,4,9,27058712072007697,342292346639241249,37181382368245040),
(11,[4228,1221,1317,1254,1319,362],61791,3,0,4,7,27058712072007697,720594848482279457,37181517659714864),
(11,[4228,1221,1317,1254,1319,426],55647,3,0,4,8,27058712072007697,594494058915905569,37181517659715088),
(12,[4228,1221,1317,1254,1319],32095,3,0,4,9,27058712072007697,594494058915905569,37181517659715088),
(12,[4228,1221,1317,1254,362],29663,3,0,4,9,27058712072007697,198177291707301921,37181517659714864),
(11,[4228,1221,1317,1254,1287,1320],64543,3,0,4,7,27058712072007697,198177291707301921,37181517659715088),
(11,[4228,1221,1317,1254,1287,1481],48415,3,0,4,8,27058712072007697,594494058915905569,37181517659715088),
(12,[4228,1221,1317,1254,1287],32543,3,1,2,10,148692184136360966,166657970532536386,92348812025186436),
(12,[4228,1221,1317,1254,1319],32159,3,0,4,9,27058712072007697,594494058915905569,37181517659715088),
(10,[4228,1221,1317,1254,1319,362,1507],96535,3,0,3,6,27058712071999505,720594839883956257,37181517659706896),
(11,[4228,1221,1317,1254,1319,362],63775,3,0,4,7,27058712072007697,720594848482279457,37181517659715088),
(11,[4228,1221,1317,1254,1319,394],63775,3,1,2,8,148692184136360966,720583132520657986,74316821345388676),
(11,[4228,1221,1317,1254,1319,426],63775,3,0,4,7,27058712072007697,594494058915905569,37181517659715088)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page9_ok : page9.all (replay raw target)=true := by decide +kernel
def page10 : List Sample := [(11,[4228,1221,1317,1254,1320,1448],56479,3,0,4,8,27058712072007697,198177291707301921,37181517659715088),
(12,[4228,1221,1317,1254,1320],32159,3,0,4,9,27058712072007697,198177291707301921,37181517659715088),
(11,[4228,1221,1317,1286,1320,362],61663,3,0,4,7,27058712072007697,198177291707301921,37181517659715088),
(12,[4228,1221,1317,1286,1320],31967,3,0,4,9,27058712072007697,198177291707301921,37181517659715088),
(12,[4228,1221,1317,1286,362],29663,3,0,4,9,27058712072007697,198177291707301921,37181517659714864),
(11,[4228,1221,1317,1286,1319,327],63775,3,0,4,7,27058712072007697,648537254444351521,37181517659715088),
(12,[4228,1221,1317,1286,1319],32159,3,0,4,9,27058712072007697,594494058915905569,37181517659715088),
(10,[4228,1221,1317,1286,327,1472,1320],112798,3,0,5,7,360295395332739138,297244767547831362,297274454952127554),
(10,[4228,1221,1317,1286,327,1320,1485],104607,3,0,4,7,27058712072007697,198177291707301921,37181517659715088),
(11,[4228,1221,1317,1286,327,1320],63647,3,0,4,7,27058712072007697,198177291707301921,37181517659715088),
(11,[4228,1221,1317,1286,327,1481],47519,3,0,7,8,360307492473032737,198177291707301921,720928000733219873),
(10,[4228,1221,1317,1286,1320,362,1507],96407,3,0,3,6,27058712071999505,198177283108978721,37181517659706896),
(11,[4228,1221,1317,1286,1320,362],63647,3,0,4,7,27058712072007697,198177291707301921,37181517659715088),
(11,[4228,1221,1317,1286,1320,394],63647,3,1,6,8,360295395332739138,297244767547831362,297274454952127554),
(11,[4228,1221,1317,1286,1320,458],63647,3,0,4,7,27058712072007697,180162893197819937,37181517659715088),
(11,[4228,1221,1317,1287,1383,1320],62559,3,0,4,7,27058712072007697,198177491423281185,37181517659715088),
(10,[4228,1221,1317,1287,1320,362,1511],94303,3,0,4,6,27058712072007697,180163092913799201,37181517659715088),
(11,[4228,1221,1317,1287,1320,362],61663,3,0,4,7,27058712072007697,198177291707301921,37181517659715088),
(10,[4228,1221,1317,1287,1320,426,1510],88223,3,0,4,7,27058712072007697,198177291707301921,37181517659715088),
(11,[4228,1221,1317,1287,1320,426],55519,3,0,4,8,27058712072007697,198177291707301921,37181517659715088),
(12,[4228,1221,1317,1287,1320],31967,3,0,4,9,27058712072007697,198177291707301921,37181517659715088),
(11,[4228,1221,1317,1287,1449,362],53727,3,0,4,8,27058712072007697,720594848482279457,37181517659715088),
(12,[4228,1221,1317,1287,1449],24031,3,0,4,10,27058712072007697,594494058915905569,37181517659715088),
(11,[4228,1221,1317,1287,362,1479],45919,3,0,4,8,27058712072007697,180163092913799201,37181517659714864),
(12,[4228,1221,1317,1287,362],29663,3,0,4,9,27058712072007697,198177291707301921,37181517659714864),
(11,[4228,1221,1317,1319,327,1478],47455,3,0,4,8,27058712072007697,720594848482279457,37181517659715088),
(11,[4228,1221,1317,1319,1383,458],45535,3,0,4,8,27058712072007697,594494258631884833,37181517659714864),
(12,[4228,1221,1317,1319,1383],30175,3,0,4,9,27058712072007697,594494258631884833,37181517659715088),
(11,[4228,1221,1317,1319,362,1475],47575,3,0,3,8,27058712071999505,720594839883956257,37181517659706896),
(12,[4228,1221,1317,1319,362],31199,3,0,4,9,27058712072007697,720594848482279457,37181517659715088),
(11,[4228,1221,1317,1319,362,1475],61911,3,0,3,7,27058712071999505,720594839883956257,37181517659706672),
(11,[4228,1221,1317,1319,362,1479],45535,3,0,4,8,27058712072007697,648537454160330785,37181517659714864),
(11,[4228,1221,1317,1319,362,460],45535,3,3,4,7,19431166908435480,342300557770279176,360314483833386288),
(11,[4228,1221,1317,327,1440,1320],55774,3,3,8,9,37181517659715088,37181517659746321,19334409673195553),
(11,[4228,1221,1317,327,1446,1320],55711,3,0,4,8,27058712072007697,198177291707301921,37181517659715088),
(11,[4228,1221,1317,327,1320,1448],55519,3,0,4,8,27058712072007697,198177291707301921,37181517659715088),
(11,[4228,1221,1317,327,1320,1451],53727,3,0,4,8,27058712072007697,180163092913799201,37181517659715088),
(11,[4228,1221,1317,327,1320,1485],39391,3,0,4,9,27058712072007697,198177291707301921,37181517659715088),
(12,[4228,1221,1317,327,1320],31199,3,0,4,9,27058712072007697,198177291707301921,37181517659715088),
(11,[4228,1221,1317,359,1449,362],53727,3,0,4,8,27058712072007697,720594848482279457,37181517659714864),
(12,[4228,1221,1317,359,1449],24031,3,0,4,10,27058712072007697,594494058915905569,37181309353801232),
(12,[4228,1221,1317,359,362],29663,3,0,4,9,27058712072007697,198177291707301921,37181517659714864),
(11,[4228,1221,1317,1383,1320,426],53727,3,0,4,8,27058712072007697,198177491423281185,37181517659715088),
(12,[4228,1221,1317,1383,1320],30175,3,0,4,9,27058712072007697,198177491423281185,37181517659715088),
(11,[4228,1221,1317,391,1440,362],54238,3,2,3,6,19431166908435480,342300557770279176,360314483833386288),
(11,[4228,1221,1317,391,1442,362],54235,3,0,3,8,27058712072007697,342292479783227425,37181517659714864),
(11,[4228,1221,1317,391,1443,362],54231,3,0,3,8,27058712072007697,342292479783227425,37181517659714864),
(11,[4228,1221,1317,391,1446,362],54175,3,0,4,8,27058712072007697,198177291707301921,37181517659714864),
(11,[4228,1221,1317,391,1448,362],53983,3,0,4,8,27058712072007697,342292479783227425,37181517659714864),
(11,[4228,1221,1317,391,362,1485],37855,3,0,4,9,27058712072007697,342292479783227425,37181517659714864),
(12,[4228,1221,1317,391,362],29663,3,0,4,9,27058712072007697,342292479783227425,37181517659714864),
(12,[4228,1221,1317,1415,362],29663,3,0,4,9,27058712072007697,198177291707301921,180170805828855088),
(11,[4228,1221,1317,1320,362,1475],47575,3,0,3,8,27058712071999505,198177283108978721,37181517659706896),
(12,[4228,1221,1317,1320,362],31199,3,0,4,9,27058712072007697,198177291707301921,37181517659715088),
(11,[4228,1221,1317,1320,362,1475],61911,3,0,3,7,27058712071999505,198177283108978721,37181517659706896),
(11,[4228,1221,1317,1320,362,1479],45535,3,0,4,8,27058712072007697,180163092913799201,37181517659715088),
(12,[4228,1221,1317,1320,426],31199,3,0,4,9,27058712072007697,180162893197819937,37181517659715088),
(11,[4228,1221,1317,1384,362,1475],46039,3,0,3,8,27058712071999505,198177283108978721,37181517659706672),
(12,[4228,1221,1317,1384,362],29663,3,0,4,9,27058712072007697,198177291707301921,37181517659714864),
(12,[4228,1221,1317,1416,362],29663,3,3,4,7,19431166908435480,342300557770279176,360314483833418032),
(12,[4228,1221,1317,362,1442],29663,3,0,4,9,27058712072007697,198177291707301921,37181517659714864),
(11,[4228,1221,1317,362,1443,1447],54231,3,0,3,8,27058712071999505,198177283108978721,37181517659706672),
(11,[4228,1221,1317,362,1443,1448],54231,3,0,3,8,27058712071999505,198177283108978721,37181517659706672),
(12,[4228,1221,1317,362,1447],29663,3,0,4,9,27058712072007697,198177291707301921,37181517659714864)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page10_ok : page10.all (replay raw target)=true := by decide +kernel
def page11 : List Sample := [(11,[4228,1221,1317,362,1447,460],37855,3,3,4,7,19431166908435480,342300557770279176,360314483833386288),
(12,[4228,1221,1317,362,1448],29663,3,0,4,9,27058712072007697,198177291707301921,37181517659714864),
(11,[4228,1221,1317,362,428,1479],37855,3,0,4,9,27058712072007697,180163092913799201,180170805828791600),
(12,[4228,1221,1317,362,1452],29663,3,3,4,7,19431166908435480,342300557770279176,360314483833386288),
(12,[4228,1221,1254,1319,394],27519,3,0,4,5,27058712072007697,198177291707301921,37181309126259888),
(11,[4228,1221,1254,1287,1320,1385],62527,3,1,2,7,148692184136360966,166658203534512194,92348812025186436),
(12,[4228,1221,1254,1287,1320],32319,3,1,2,9,148692184136360966,166657970532536386,92348812025186436),
(12,[4228,1221,1254,1287,1385],30527,3,1,2,9,148692184136360966,166658203534512194,92348812025186436),
(12,[4228,1221,1254,1287,1449],24383,3,1,2,10,148692184136360966,166657970532536386,92348812025186436),
(11,[4228,1221,1254,1287,362,1475],47927,3,1,2,8,148692184136352774,148625971238686786,92331219854870660),
(12,[4228,1221,1254,1287,362],31551,3,1,2,9,148692184136360966,148625979837009986,92331219854870660),
(12,[4228,1221,1254,1287,394],31551,3,1,2,9,148692184136360966,166639837187952722,92330686205184148),
(11,[4228,1221,1254,1319,362,1475],47927,3,1,2,8,148692184136352774,720583123914994754,92331219854870660),
(12,[4228,1221,1254,1319,362],31551,3,1,2,9,148692184136360966,720583132513317954,92331219854870660),
(11,[4228,1221,1254,1320,426,1479],39743,3,1,2,9,148692184136360966,720583132520657986,74316821345388676),
(11,[4228,1221,1286,1318,1320,362],61631,3,1,4,8,27094993604785234,594482179745271890,720595064530013266),
(12,[4228,1221,1286,1318,1320],31935,3,3,4,11,19431166908435480,594501755724747016,360314582617634320),
(12,[4228,1221,1286,1318,362],29631,3,3,4,7,19431166908435480,378328973610963208,360314582617634128),
(12,[4228,1221,1286,1320,1385],29951,3,3,4,10,19431166908435480,594501755724679432,360314582617634320),
(11,[4228,1221,1286,1320,362,1481],45311,3,5,7,9,148655668798239904,360324370848101664,360433322357241472),
(12,[4228,1221,1286,1319,327],31551,3,0,4,5,27058712072007697,198177291707301921,37181309126259888),
(12,[4228,1221,1286,1320,1445],32415,3,1,8,9,342298589001961538,297244767540491330,297274454952127554),
(10,[4228,1221,1286,1320,1385,362,1507],94391,3,1,3,6,27094993604777042,297244758942168130,297818172041997394),
(11,[4228,1221,1286,1320,1385,362],61631,3,1,4,7,27094993604785234,297244767540491330,297818172041997394),
(12,[4228,1221,1286,1320,1385],31935,3,3,4,10,19431166908435480,594501755724679432,360314582617634320),
(11,[4228,1221,1286,1320,426,1477],47775,3,1,7,8,378309793842221122,297244767547831362,297274454952127554),
(11,[4228,1221,1286,1385,362,1475],46007,3,1,3,8,27094993604777042,648525529877066818,649098942976896082),
(12,[4228,1221,1286,1385,362],29631,3,1,4,9,27094993604785234,648525538475421762,649098942976927826),
(11,[4228,1221,1287,1320,1385,394],57599,3,3,4,8,19431166908435480,594501755724679432,648544958769346064),
(12,[4228,1221,1287,1320,1385],29951,3,3,4,10,19431166908435480,594501755724679432,648544958769346064),
(12,[4228,1221,1319,327,1446],23423,3,0,4,5,27058712072007697,198177291707301921,37181309126259888),
(12,[4228,1221,1319,327,1384],29567,3,0,4,5,27058712072007697,198177905887625249,37181517432173744),
(10,[4228,1221,327,1408,1320,459,1511],74622,3,1,3,8,27167330721212564,37161891400829060,37181517659746321),
(11,[4228,1221,327,1320,1416,1385],57599,3,3,4,8,19431166908435480,594501755724679432,648544958769346064),
(11,[4228,1221,327,1320,427,1479],37759,3,0,4,5,27058712072007697,198177905887625249,37181517432173744),
(11,[4228,1221,362,1411,423,1478],46007,3,1,3,10,27094314999944274,378309552234582082,649099320271341650),
(12,[4228,1253,1317,1409,362],29663,3,0,4,9,27058712072007697,342292679499335713,180170805828791600),
(11,[4228,1253,1317,1254,1319,426],55647,3,0,4,8,27058712072007697,594494258631884833,180170805828791824),
(12,[4228,1253,1317,1254,1319],32095,3,0,4,9,27058712072007697,594494258631884833,180170805828791824),
(11,[4228,1253,1317,1286,1320,362],61663,3,0,4,7,27058712072007697,198177491423281185,180170805828791824),
(11,[4228,1253,1317,1286,1320,426],55519,3,0,4,8,27058712072007697,180163092913799201,180170805828791824),
(12,[4228,1253,1317,1286,1320],31967,3,0,4,9,27058712072007697,198177491423281185,180170805828791824),
(12,[4228,1253,1317,1286,362],29663,3,0,4,9,27058712072007697,198177491423281185,180170805828791600),
(11,[4228,1253,1317,326,1443,1319],55767,3,0,3,8,27058712071999505,594494258631884833,180170805828791824),
(11,[4228,1253,1317,326,1443,1320],55767,3,0,3,8,27058712071999505,180163092913799201,180170805828791824),
(11,[4228,1253,1317,326,1319,1447],55647,3,0,4,8,27058712072007697,648537454160330785,180170805828791824),
(11,[4228,1253,1317,326,1319,1451],53727,3,0,4,8,27058712072007697,648537454160330785,37181517659715088),
(12,[4228,1253,1317,326,1319],31199,3,0,4,9,27058712072007697,594494258631884833,180170805828791824),
(11,[4228,1253,1317,326,1320,1448],55519,3,0,4,8,27058712072007697,180163092913799201,180170805828791824),
(10,[4228,1253,1317,326,1320,1451,1287],118879,3,0,4,6,27058712072007697,180163092913799201,37181517659715088),
(11,[4228,1253,1317,326,1320,1451],53727,3,0,4,8,27058712072007697,180163092913799201,37181517659715088),
(12,[4228,1253,1317,326,1320],31199,3,0,4,9,27058712072007697,180163092913799201,180170805828791824),
(11,[4228,1253,1317,390,362,1485],37855,3,0,4,9,27058712072007697,198177491423281185,180170805828791600),
(12,[4228,1253,1317,390,362],29663,3,0,4,9,27058712072007697,198177491423281185,180170805828791600),
(12,[4228,1253,1317,1414,362],29663,3,3,4,7,19431166908435480,342300557770279176,360314483833386288),
(11,[4228,1253,1317,1320,362,1478],45535,3,0,4,8,27058712072007697,198177491423281185,37181517659715088),
(12,[4228,1253,1317,1320,426],31199,3,0,4,9,27058712072007697,180163092913799201,180170805828791824),
(12,[4228,1253,1317,1416,362],29663,3,0,4,9,27058712072007697,342292679499206689,324278297323506992),
(11,[4228,1253,1317,362,1446,460],37855,3,3,4,7,19431166908435480,342300557770279176,360314483833386288),
(12,[4228,1253,1254,1318,394],27583,3,1,4,10,27094993604785234,378309381518020674,74336214583487570),
(12,[4228,1253,1254,1319,394],27519,3,0,4,5,27058712072007697,198177491423281185,180170805601250480),
(12,[4228,1253,1318,326,1447],23487,3,1,4,10,27094993604785234,378309397631488066,74336214583487570),
(12,[4228,1253,1318,326,1320],31167,3,1,4,9,27094993604785234,594482179745271890,720595064530013266),
(12,[4228,1285,1254,1318,394],27583,3,1,4,10,27094993604785234,378309381518020674,74336214583487570)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page11_ok : page11.all (replay raw target)=true := by decide +kernel
def page12 : List Sample := [(12,[4228,1285,1254,1319,394],27519,3,0,4,5,27058712072007697,324278695454068769,324278297095965872),
(12,[4228,1285,1318,326,1447],23487,3,1,4,10,27094993604785234,378309397631488066,74336214583487570),
(12,[4228,1317,230,1413,1320],28127,3,0,4,9,27058712072007697,198177291707301921,180170805828855312),
(12,[4228,1317,230,1320,1416],27903,3,3,4,10,19431166908435480,594501755724679432,648544859985130000),
(11,[4228,1317,1254,1413,1319,394],59743,3,0,4,7,27058712072007697,594494258631884833,37181517659715088),
(11,[4228,1317,1254,1413,1319,426],55647,3,0,4,7,27058712072007697,594494258631884833,37181517659714864),
(12,[4228,1317,1254,1413,1319],32095,3,0,4,8,27058712072007697,594494258631884833,37181517659715088),
(12,[4228,1317,1254,1413,426],23519,3,0,4,9,27058712072007697,198177491423281185,37181517659714864),
(12,[4228,1317,1254,1382,1319],32063,3,1,2,9,148692184136360966,648525771477365826,92348812025186436),
(11,[4228,1317,1254,1319,394,1477],43487,3,0,4,8,27058712072007697,594494258631884833,37181517659715088),
(11,[4228,1317,1254,1319,362,1478],47423,3,1,2,8,148692184136360966,648525771484705858,648525773835611268),
(11,[4228,1317,1254,1319,394,1477],47455,3,0,4,7,27058712072007697,594494258631884833,37181517659715088),
(11,[4228,1317,1254,1319,394,1477],59743,3,0,4,7,27058712072007697,594494258631884833,37181517659715088),
(11,[4228,1317,1254,1320,394,1477],43487,3,0,4,8,27058712072007697,594494258631954465,37181517659715088),
(11,[4228,1317,326,1411,1287,1320],59639,3,3,8,10,297256699331742744,648544859985121808,594501747134744840),
(10,[4228,1317,326,1411,1287,459,1510],74679,3,1,3,8,27094993604777042,27112585775140930,297256699331742744),
(11,[4228,1317,326,1413,1319,1480],43487,3,0,4,8,27058712072007697,720594848482279457,37181517659715088),
(11,[4228,1317,326,1413,1320,1287],59615,3,0,4,7,27058712072007697,594494058915975201,37181517659715088),
(11,[4228,1317,326,1287,1320,1419],57599,3,3,4,9,19431166908435480,594501755724679432,648544859985098256),
(12,[4228,1317,326,1287,1320],30975,3,3,4,11,19431166908435480,594501755724679432,648544859985130000),
(11,[4228,1317,326,1287,427,1478],37823,3,3,4,7,19431166908435480,378329354789310728,360314582617634128),
(11,[4228,1317,326,1319,1415,1477],59743,3,0,4,7,27058712072007697,594494258631884833,37181517659715088),
(11,[4228,1317,358,1319,327,1484],43391,3,2,4,9,27167563723189396,594481872842573956,720602625821749396),
(12,[4228,1317,358,1319,327],31103,3,2,4,10,27167563723189396,594482044656994452,648545031783821460),
(11,[4228,1317,358,1319,1415,458],43391,3,2,4,9,27167563723189396,594481864252639364,720602625821749396),
(12,[4228,1317,358,1320,1416],27903,3,3,4,10,19431166908435480,594501655866689800,360314483833418256),
(11,[4228,1317,1382,1319,327,1478],47423,3,1,2,10,148692184136360966,648525771484705858,74316821329660036),
(12,[4228,1317,1382,1319,327],31103,3,2,4,10,27167563723189396,594482044656994452,648545031783821460),
(12,[4228,1317,1319,1286,327],31103,3,2,4,9,27167563723189396,594482044656994452,648545031783821460),
(11,[4228,1317,1319,327,1446,1477],55647,3,0,4,7,27058712072007697,594494258631884833,37181517659715088),
(12,[4228,1317,1319,327,1384],31103,3,2,4,9,27167563723189396,594482044656994452,648545031783821460),
(11,[4228,1317,327,1413,1286,1320],59615,3,0,4,7,27058712072007697,594494258631954465,180170805828791824),
(12,[4228,1317,327,1286,1320],30975,3,3,4,11,19431166908435480,594501755724679432,360314483833386512),
(11,[4228,1317,359,1414,1445,458],43935,3,0,4,8,27058712072007697,198177291707301921,37181517659714864),
(12,[4228,1254,1381,1319,362],29567,3,0,4,5,27058712072007697,198177491423281185,37181517432173744),
(12,[4228,1254,1318,1413,362],29631,3,3,4,7,19431166908435480,324286159260797192,360314582617634128),
(12,[4228,1254,1318,1416,362],29631,3,1,4,9,27094993604785234,378309381518020674,360307094340373586),
(12,[4228,1254,1318,362,1445],29631,3,1,4,9,27094993604785234,378309381518020674,74336214583487570),
(12,[4228,1254,1318,362,1448],29631,3,1,4,9,27094993604785234,378309381518020674,74336214583487570),
(12,[4228,1254,1318,362,1452],29631,3,3,4,7,19431166908435480,324286159260797192,360314582617634128),
(12,[4228,1254,1319,362,1452],29567,3,0,4,5,27058712072007697,198177905887625249,37181517432173744),
(11,[4228,1254,1384,394,1318,1320],59583,3,0,4,5,27058712072007697,198177905887625249,37181517432173872),
(12,[4228,1254,1384,394,1320],27391,3,0,4,5,27058712072007697,198177905887625249,37181517432173872),
(12,[4228,1318,326,1415,1445],27583,3,1,4,9,27094993604785234,378309397631488066,74336214583487570),
(12,[4228,1318,326,1415,1448],27583,3,1,4,9,27094993604785234,378309397631488066,74336214583487570),
(12,[4228,327,1382,1285,1319],29567,3,0,4,5,27058712072007697,324278695454068769,324278297095965872),
(12,[4261,1217,1252,1316,426],23535,3,0,4,10,180163507378143265,63087509090971665,594512031908375608),
(12,[4261,1281,1252,1316,426],23535,3,0,4,10,180163507378143265,63087509090971665,594512031908375608),
(12,[4261,1154,1318,1320,394],27135,3,0,4,5,27058712072007697,180163507378143265,37181517432174128),
(12,[4261,1250,1220,1284,394],27631,3,0,4,10,180163507378143265,63086894910648337,27058479459022384),
(12,[4261,1250,1318,1320,394],27135,3,0,4,5,27058712072007697,180163507378143265,37181517432174128),
(12,[4261,1314,1220,1284,394],27631,3,0,4,10,180163507378143265,63086894910648337,27058479459022384),
(12,[4261,1220,1284,1254,362],29679,3,0,4,9,180163507378143265,63086894910648337,27058479459022384),
(11,[4261,1220,1284,1318,1320,362],61679,3,0,4,7,180163507378143265,63086894910648337,27058479459022112),
(12,[4261,1220,1284,1318,1320],31983,3,0,4,9,180163507378143265,63086894910648337,27058479459022112),
(12,[4261,1220,1284,1318,362],29679,3,0,4,9,180163507378143265,63086894910648337,27058479459022384),
(11,[4261,1220,1284,1318,327,1320],63663,3,0,4,7,180163507378143265,27058097891684369,27058479459022112),
(11,[4261,1220,1284,1318,1320,362],63663,3,0,4,7,180163507378143265,63086894910648337,27058479459022112),
(11,[4261,1220,1284,1318,1320,394],63663,3,1,6,8,648525771484705858,648525375273717826,720595064530013250),
(11,[4261,1220,1284,1318,1320,458],63663,3,0,4,7,180163507378143265,27058097891684369,27058479459022112),
(12,[4261,1220,1284,1319,362],29679,3,0,4,9,180163507378143265,63086894910648337,27058479459022384),
(12,[4261,1220,1284,327,1320],31471,3,0,4,9,180163507378143265,27058097891684369,27058479459022112),
(12,[4261,1220,1284,359,362],29679,3,0,4,9,180163507378143265,63086894910648337,27058479459022384),
(12,[4261,1220,1284,391,362],29679,3,0,4,9,180163507378143265,63086894910648337,27058479459022384)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page12_ok : page12.all (replay raw target)=true := by decide +kernel
def page13 : List Sample := [(12,[4261,1220,1284,1320,362],31471,3,0,4,9,180163507378143265,63086894910648337,27058479459022112),
(12,[4261,1220,1284,1320,426],31471,3,0,4,9,180163507378143265,27058097891684369,27058479459022112),
(12,[4261,1220,1284,362,1442],29679,3,0,4,9,180163507378143265,63086894910648337,27058479459022384),
(12,[4261,1220,1284,362,1447],29679,3,0,4,9,180163507378143265,63086894910648337,27058479459022384),
(12,[4261,1220,1284,362,1449],29679,3,0,4,9,180163507378143265,63086894910648337,27058479459022384),
(12,[4261,1220,1284,362,428],29679,3,4,6,8,148655669009003680,648554755589748272,630680302147127936),
(11,[4261,1220,1284,394,1447,459],37871,3,0,4,9,180163507378143265,63086894910648337,27198117435876912),
(11,[4261,1220,1286,1318,1320,362],61631,3,1,5,7,37228092669899874,297244767451362402,297274454952127586),
(12,[4261,1220,1286,1318,1320],31935,3,5,6,11,148655669009003680,360324379438036256,360433329873434240),
(12,[4261,1220,1286,1318,362],29631,3,5,6,8,148655669009003680,648554755589748320,648663706025145984),
(12,[4261,1220,1318,1320,1384],29951,3,3,4,10,19430785730087960,324320962454538504,360314582617634320),
(11,[4261,1220,1318,1320,362,1480],45311,3,3,4,9,19430785730087960,594501755724714248,360314582617634320),
(11,[4261,1220,1318,1287,327,1320],63551,3,3,8,10,180170971184941320,648544951253192968,648694484607021320),
(12,[4261,1220,1318,1320,1444],32175,3,1,8,9,594482575956259906,594482179745271874,720595064530013250),
(11,[4261,1220,1318,1320,1384,362],61631,3,1,5,7,37228092669899874,360294999122006082,360604684034265186),
(12,[4261,1220,1318,1320,1384],31935,3,5,6,10,148655669009003680,360324379438036256,324435319180020352),
(11,[4261,1220,1318,1320,426,1476],47535,3,1,7,8,594482575956259906,594482179745271874,720595064530013250),
(12,[4261,1220,1318,1384,362],29631,3,1,5,9,37228092669899874,360294999122006082,360604684034265186),
(12,[4261,1252,1316,1254,394],27631,3,0,4,9,180163507378143265,63087509090971665,594512031908375608),
(12,[4261,1252,1316,1286,394],27631,3,0,4,9,180163507378143265,63087509090971665,594512031908375608),
(12,[4261,1252,1316,358,394],27631,3,0,4,9,180163507378143265,63087509090971665,594512031908375608),
(12,[4261,1252,1316,390,394],27631,3,0,4,9,180163507378143265,63087509090971665,594512031908375608),
(12,[4261,1252,1316,1287,394],27631,3,0,4,9,180163507378143265,63087509090971665,594512031908375608),
(11,[4261,1252,1316,362,1446,460],35823,3,3,4,7,180170589317840952,324321343632886024,360324851884438816),
(11,[4261,1252,1316,362,1448,460],35823,3,0,4,9,180163507378143265,63087509090971665,594792407373712440),
(12,[4261,1252,1316,394,1441],27631,3,0,4,9,180163507378143265,63087509090971665,594512031908375608),
(12,[4261,1252,1316,394,422],27631,3,0,4,9,180163507378143265,63087509090971665,594512031908375608),
(12,[4261,1252,1316,394,1446],27631,3,0,4,9,180163507378143265,63087509090971665,594512031908375608),
(12,[4261,1252,1316,394,1447],27631,3,0,4,9,180163507378143265,63087509090971665,594512031908375608),
(12,[4261,1252,1316,394,1448],27631,3,0,4,9,180163507378143265,63087509090971665,594512031908375608),
(12,[4261,1252,1254,1318,426],23487,3,1,5,10,37227696459166818,648525771484705858,648555225500101730),
(12,[4261,1252,1254,326,1287],31551,3,1,2,9,148692184136360966,148625979747881058,110345084714666116),
(12,[4261,1252,1254,326,1449],23487,3,1,5,10,37227696459166818,648525771484705858,648555225500101730),
(12,[4261,1252,1286,326,1320],31423,3,1,5,9,37228092669899874,297244767451362402,297274454952127586),
(12,[4261,1252,1286,326,1385],29631,3,5,6,8,148936044474290336,720751987604467296,594651505128163968),
(11,[4261,1252,1318,1320,1384,394],57599,3,3,4,8,19430785730087960,324285778082449672,297264187834510864),
(12,[4261,1252,1318,1320,1384],29951,3,3,4,10,19430785730087960,324320962454538504,297264187834510864),
(11,[4261,1252,1318,1320,362,1480],45311,3,3,4,9,19430785730087960,648544951253160200,648580143141466640),
(11,[4261,1252,326,1320,1384,1417],57599,3,3,4,8,19430785730087960,324285778082449672,297264187834510864),
(11,[4261,1284,230,1412,1320,426],51951,3,0,4,8,180163507378143265,63086894910648337,27198117435876640),
(12,[4261,1284,230,1412,1320],28399,3,0,4,9,180163507378143265,324295673298593809,27198117435876640),
(11,[4261,1284,230,1412,362,1481],41967,3,0,4,9,180163507378143265,63087509090971665,19457554976738360),
(12,[4261,1284,230,1320,1417],27903,3,5,7,10,148655669009003680,720751987604530464,324435319180020352),
(11,[4261,1284,1254,1318,1320,426],55487,3,1,5,8,37227696459166818,648525771484705858,648555225500101730),
(12,[4261,1284,1254,1318,426],23487,3,1,5,10,37227696459166818,648525771484705858,648555225500101730),
(12,[4261,1284,1254,326,1319],31551,3,1,2,9,148692184136360966,720583132424189026,110345618364352644),
(11,[4261,1284,1254,326,1320,1449],55487,3,1,5,8,37227696459166818,648525771484705858,648555225500101730),
(12,[4261,1284,1254,326,1449],23487,3,1,5,10,37227696459166818,648525771484705858,648555225500101730),
(11,[4261,1284,1318,327,1320,1451],53503,3,3,4,9,19430785730087960,324285778082449672,297264187834510864),
(12,[4261,1284,1318,1320,362],30975,3,5,7,10,148655669009003680,648554755589748000,324435319180020352),
(12,[4261,1284,358,1320,1417],27903,3,5,7,10,148655669009003680,720751987604537632,324435319180020352),
(11,[4261,1316,230,1412,362,1480],41967,3,0,4,9,180163507378143265,63087509090971665,19457554976738360),
(12,[4261,1316,1254,326,1287],31551,3,1,2,9,148692184136360966,148625979747881058,110345618364352644),
(12,[4261,1316,1254,326,1416],27583,3,5,6,8,148655196562601120,720751987604537952,648663914331067008),
(11,[4261,1316,326,1287,427,1478],37823,3,5,6,8,148655669009003680,648554755589748320,594651505128163968),
(12,[4261,1254,1380,326,1287],31551,3,1,2,8,148692184136360966,148625438582001762,110345084714666116),
(11,[4261,1254,1286,1318,1320,362],61631,3,1,5,7,37228092669899874,297244767451362402,297274454952127586),
(12,[4261,1254,1286,1318,1320],31935,3,3,4,11,19431133622438936,594501755724714248,360314582617634320),
(11,[4261,1254,1318,1287,1320,362],61567,3,3,4,9,19431166908435480,648544951253160200,648544958769346064),
(12,[4261,1254,1318,1287,1320],31871,3,3,4,11,19431133622438936,648544951253160200,648544958769346064),
(12,[4261,1254,1318,1320,1384],29951,3,3,4,10,19431133622438936,594501755724714248,360314582617634320),
(11,[4261,1254,1318,1320,362,1480],45311,3,3,4,9,19431166908435480,594501755724714248,360314582617634320),
(11,[4261,1254,1318,1287,1320,394],59583,3,0,4,5,27058712072007697,180163507378143265,37181517432174128),
(12,[4261,1254,1318,1287,1320],31935,3,3,4,11,19431133622438936,648544951253160200,648544958769346064)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page13_ok : page13.all (replay raw target)=true := by decide +kernel
def page14 : List Sample := [(12,[4261,1254,1318,1287,394],27583,3,1,5,9,37227696459166818,648525771484705858,648555225500101730),
(11,[4261,1254,1318,1287,1320,362],63551,3,3,4,9,19431166908435480,648544951253160200,648544958769346064),
(11,[4261,1254,1318,1287,1320,426],63551,3,1,2,6,148692184136360966,148626212846325826,648525773835611268),
(11,[4261,1254,1318,1287,1320,458],63551,3,1,2,6,148692184136360966,148626212846325826,648525773835611268),
(12,[4261,1254,1318,1287,426],31551,3,1,2,8,148692184136360966,148626212846325826,648525773835611268),
(11,[4261,1254,1318,1320,1447,394],59711,3,0,4,5,27058712072007697,180163507378143265,37181517432174128),
(11,[4261,1254,1318,1320,1447,426],55615,3,0,4,5,27058712072007697,630523470115192865,37181309126260272),
(12,[4261,1254,1318,1320,1447],32063,3,1,2,8,148692184136360966,148626212846325826,648525773835611268),
(11,[4261,1254,1318,1320,1384,362],61631,3,1,5,9,37228092669899874,297244767451362402,297274454952127586),
(11,[4261,1254,1318,1320,1384,394],59583,3,0,4,5,27058712072007697,180163507378143265,37181517432174128),
(12,[4261,1254,1318,1320,1384],31935,3,3,4,10,19431133622438936,594501755724714248,360314582617634320),
(11,[4261,1254,1318,1320,362,1480],47295,3,3,4,9,19431166908435480,594501755724714248,360314582617634320),
(11,[4261,1254,1318,1320,426,1479],47423,3,1,2,7,148692184136360966,148626212846325826,648525773835611268),
(12,[4261,1254,326,1287,1319],31551,3,1,2,8,148692184136360966,684554335405256802,110345618364352644),
(11,[4261,1254,326,1287,1320,1417],59583,3,1,5,7,37227696459166818,648525771484705858,648555225500101730),
(12,[4261,1254,326,1287,1417],27583,3,1,5,9,37227696459166818,648525771484705858,648555225500101730),
(12,[4261,1254,326,1287,1444],31551,3,1,2,8,148692184136360966,148625979747881058,110345618364352644),
(12,[4261,1254,326,1287,1385],31551,3,1,2,8,148692184136360966,684554335405256802,684554570854606980),
(12,[4261,1254,326,1287,1449],31551,3,1,2,8,148692184136360966,148625979747881058,110345618364352644),
(12,[4261,1254,326,1319,1444],31551,3,1,2,8,148692184136360966,720583132424189026,110345618364352644),
(12,[4261,1254,326,1319,1448],31551,3,1,2,8,148692184136360966,720583132424189026,110345618364352644),
(11,[4261,1254,326,1320,1447,1417],59711,3,1,2,7,148692184136360966,148626212846325826,110345618364352644),
(12,[4261,1254,326,1320,1447],31551,3,1,2,8,148692184136360966,148625979747881058,110345618364352644),
(11,[4261,1254,326,1320,1384,1417],59583,3,3,4,8,19431166908435480,594501755724714248,360314582617634320),
(12,[4261,1254,326,1384,1385],29631,3,5,6,8,148655196562601120,648554755589748320,648663914331059840),
(12,[4261,1254,326,1384,1444],29631,3,5,6,8,148655196562601120,648554755589748320,648663914331059840),
(12,[4261,1254,326,1384,1449],29631,3,5,6,8,148655196562601120,648554755589748320,648663914331059840),
(11,[4261,1286,1318,327,1446,1320],55487,3,3,4,10,19431166908435480,594501755724747016,360314582617634320),
(11,[4261,1286,1318,327,1320,1451],53503,3,3,4,9,19431166908435480,594501755724747016,360314582617634320),
(12,[4261,1286,1318,327,1320],30975,3,3,4,11,19431166908435480,594501755724747016,360314582617634320),
(12,[4261,1286,326,1320,1444],31423,3,1,5,8,37228092669899874,297244767451362402,297274454952127586),
(12,[4261,1286,326,1320,423],31423,3,1,5,8,37228092669899874,297244767451362402,297274454952127586),
(12,[4261,1286,326,1320,1447],31423,3,1,5,8,37228092669899874,297244767451362402,297274454952127586),
(11,[4261,1318,1287,327,1446,1320],55423,3,3,4,10,19431166908435480,648544951253192968,648544958769346064),
(12,[4261,1318,1287,1320,394],30975,3,3,4,10,19431166908435480,648544951253192968,648544958769346064),
(11,[4261,1318,327,1414,1320,1448],59583,3,3,4,9,19431166908435480,594501755724747016,360314582617634320),
(12,[4261,1318,1320,1410,362],29183,3,0,4,5,27058712072007697,180163507378143265,37181517432174128),
(12,[4261,1318,1320,1412,362],29183,3,0,4,5,630541062140110865,180163507378143265,324278297095966256),
(11,[4261,1318,1320,391,1446,362],53695,3,0,4,5,27058712072007697,180163507378143265,37181517432174128),
(12,[4261,1318,1320,391,362],29183,3,0,4,5,27058712072007697,180163507378143265,37181517432174128),
(12,[4261,1318,1320,1415,362],29183,3,0,4,5,27058712072007697,180163507378143265,37181517432174128),
(12,[4261,1318,1320,1415,394],27135,3,0,4,5,27058712072007697,684566665643638817,37181309126260272),
(12,[4261,326,1287,1412,1414],27583,3,5,6,8,148935572027887776,648554755589748320,648663914331067008),
(11,[4261,326,1320,391,1446,1385],53695,3,1,5,9,37227696459166818,648525771484705858,648555225500101730),
(11,[4261,1287,358,327,1320,1417],59519,3,3,4,9,19431166908435480,720602545291215112,297264187834510864),
(11,[4261,1287,358,1320,1417,426],51455,3,0,4,5,27058712072007697,684566665643638817,37181309126260272),
(12,[4261,1287,358,1320,1417],27903,3,3,4,10,19431133622438936,720602545291215112,297264187834510864),
(11,[4261,327,1320,1384,422,1481],45311,3,3,4,8,19431166908435480,720602545291215112,297264187834510864),
(11,[4294,1345,1188,1252,1317,1319],63823,3,2,8,10,720583367873539204,720582834223368324,648615400527999108),
(12,[4294,1345,1188,1252,1317],31695,3,3,6,9,324286159260797192,19430719158094872,27312699419536672),
(10,[4294,1345,1188,1284,1317,1320,395],123087,3,0,4,6,74346507955914833,99186060470366289,297871110737243217),
(11,[4294,1345,1188,1284,1317,395],58319,3,0,4,8,74346507955914833,99186060470366289,595108686143727697),
(11,[4294,1345,1188,1284,1320,395],58095,3,0,4,8,252290855518552161,99186060470366289,99186441852106016),
(11,[4294,1345,1188,1317,1319,395],57823,3,0,4,8,99186060470366289,720665216765083745,109309480214279696),
(12,[4294,1345,1188,1317,1319],31199,3,5,7,10,324331965087009088,720648732295704128,720866643676376352),
(11,[4294,1345,1188,1317,1415,459],41951,3,0,5,9,74346507859445857,252291055695904801,180216769495051361),
(11,[4294,1345,1188,1317,1320,395],57823,3,0,4,8,99186060470366289,252290855518552161,109309480214279696),
(11,[4294,1345,1188,1317,395,1479],41951,3,0,5,9,74346507859445857,180233461657976865,180216769495051361),
(11,[4294,1345,1252,1317,1319,395],57727,3,1,2,6,220749778174288902,360295395332739138,74316821141964996),
(11,[4294,1345,1253,1317,1287,1320],63583,3,0,4,8,99186674854113297,252291055695904801,180170805828791824),
(12,[4294,1345,1253,1317,1320],31199,3,0,4,10,99186674854113297,252291055695904801,180170805828791824),
(11,[4294,1345,1317,1287,1320,395],57599,3,3,4,9,19431166908435480,594501755724679432,648544791265621520),
(11,[4294,1345,1317,1287,1320,427],53503,3,3,4,9,19431166908435480,594501689152686344,360314483833386512),
(12,[4294,1345,1317,1287,1320],30975,3,3,4,11,19431166908435480,594501689152686344,648615160009830928)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page14_ok : page14.all (replay raw target)=true := by decide +kernel
def page15 : List Sample := [(12,[4294,1250,1188,1284,394],27631,3,0,5,10,74346507955914833,99186060470366289,595108686143727697),
(12,[4294,1250,1188,1317,394],27615,3,0,5,10,74346507859445857,252290855518552161,324611233524502625),
(12,[4294,1282,1188,1317,394],27615,3,0,5,10,74346507859445857,252290855518552161,324611233524502625),
(12,[4294,1314,1188,1284,394],27631,3,0,5,10,74346507955914833,99186060470366289,595108686143727697),
(10,[4294,1346,1188,1284,1317,1320,395],123087,3,0,4,6,74346507955914833,99186060470366289,297871110737243217),
(11,[4294,1346,1188,1284,1317,395],58319,3,0,4,8,74346507955914833,99186060470366289,595108686143727697),
(11,[4294,1346,1188,1284,1320,395],58095,3,0,4,8,252290855518552161,99186060470366289,99186441852106016),
(11,[4294,1346,1188,1317,1320,395],57823,3,0,4,8,99186060470366289,252290855518552161,109309480214279696),
(12,[4294,1188,1378,1317,362],29663,3,0,5,10,74346507859445857,252290722374565985,324611100380516449),
(11,[4294,1188,1252,1317,1319,1351],63823,3,2,7,9,720583367873539204,720582834223368324,648615400527999108),
(12,[4294,1188,1252,1317,1319],32207,3,3,6,8,324286159260797192,19430719158094872,27312699419536672),
(11,[4294,1188,1252,1317,1319,1352],63823,3,2,7,9,720583367873539204,720582834223368324,648615400527999108),
(11,[4294,1188,1252,1317,1319,362],63823,3,2,7,9,720583367873539204,720582834223368324,648615400527999108),
(11,[4294,1188,1252,1317,1319,394],63823,3,3,5,6,324286159260797192,19430719158094872,27312699419536672),
(11,[4294,1188,1252,1317,1319,426],63823,3,2,7,9,720583367873539204,720582834223368324,648545031783821444),
(11,[4294,1188,1252,1317,1319,1450],63823,3,2,7,9,720583367873539204,720582834223368324,648615400527999108),
(11,[4294,1188,1252,1317,1319,1482],63823,3,3,5,6,324286159260797192,19430785730087960,27312699419536672),
(11,[4294,1188,1252,1317,1351,461],39887,3,3,6,8,324286159260797192,19430785730087960,109564965270140192),
(12,[4294,1188,1252,1317,1351],31695,3,3,6,8,324286159260797192,19430785730087960,27312699419536672),
(11,[4294,1188,1252,1317,1320,1416],60623,3,3,7,9,19430719158094872,324285711510456584,297264020330786080),
(12,[4294,1188,1252,1317,1352],31695,3,3,6,8,324286159260797192,19430719158094872,27312699419536672),
(12,[4294,1188,1252,1317,1416],28623,3,3,6,9,324285711510456584,19430719158094872,27312698891054368),
(12,[4294,1188,1252,1317,394],31695,3,3,6,8,324286159260797192,19430719158094872,27312699419536672),
(12,[4294,1188,1252,1317,426],31695,3,3,6,8,324286159260797192,19430785730087960,27312699419536672),
(12,[4294,1188,1252,1317,1450],31695,3,3,6,8,324286159260797192,19430719158094872,27312699419536672),
(11,[4294,1188,1284,1317,1382,1320],62671,3,0,7,8,99186060470366289,252290855518552161,109309480214279456),
(11,[4294,1188,1284,1317,1319,327],63823,3,1,2,4,220749778174288902,360295395332739138,74316821141964996),
(11,[4294,1188,1284,1317,1319,362],61903,3,0,4,7,74346507955914833,99186060470366289,595108686143727697),
(12,[4294,1188,1284,1317,1319],32207,3,4,6,10,324331965087009088,720648732295704128,648870621761192224),
(10,[4294,1188,1284,1317,327,1320,1518],80079,3,6,7,8,297274457101708576,720594929240640800,720866508384906528),
(10,[4294,1188,1284,1317,1351,1320,459],110799,3,0,4,6,74346507955914833,99186060470366289,297871110737243217),
(10,[4294,1188,1284,1317,1351,1320,461],104655,3,6,7,8,297274457101708576,648625055614448928,648544791038112032),
(11,[4294,1188,1284,1317,1351,459],46031,3,0,4,8,74346507955914833,99186060470366289,595108686143727697),
(11,[4294,1188,1284,1317,1320,362],62671,3,0,4,7,74346507955914833,99186060470366289,297871110737243217),
(12,[4294,1188,1284,1317,362],30671,3,0,4,9,74346507955914833,99186060470366289,595108686143727697),
(11,[4294,1188,1284,1318,1320,362],61679,3,0,4,7,252290855518552161,99186060470366289,99186441852106016),
(12,[4294,1188,1284,1318,362],29679,3,0,5,9,648555460446169169,99186060470366289,595108686143727697),
(12,[4294,1188,1284,1382,1320],30447,3,0,4,9,252290855518552161,99186060470366289,99186441852106016),
(12,[4294,1188,1284,1319,327],31599,3,1,2,5,220749778174288902,360295395332739138,74316821141964996),
(12,[4294,1188,1284,1319,362],29679,3,0,5,9,74346507955914833,99186060470366289,595108686143727697),
(11,[4294,1188,1284,327,1448,362],53999,3,0,5,8,74346507955914833,99186060470366289,297310359806684241),
(12,[4294,1188,1284,327,362],29679,3,0,5,9,74346507955914833,99186060470366289,595108686143727697),
(11,[4294,1188,1284,1351,1320,427],53999,3,0,4,8,180233261480624225,99186060470366289,99186441852106016),
(12,[4294,1188,1284,359,362],29679,3,0,5,9,74346507955914833,99186060470366289,595108686143727697),
(12,[4294,1188,1284,391,362],29679,3,0,5,9,74346507955914833,99186060470366289,595108686143727697),
(12,[4294,1188,1284,1320,362],30447,3,0,4,9,252290855518552161,99186060470366289,99186441852106016),
(12,[4294,1188,1284,362,1442],29679,3,0,5,9,74346507955914833,99186060470366289,595108686143727697),
(11,[4294,1188,1284,362,423,1480],45807,3,0,5,8,74346507955914833,99186060470366289,595108686143727697),
(12,[4294,1188,1284,362,423],29679,3,0,5,9,74346507955914833,99186060470366289,595108686143727697),
(12,[4294,1188,1284,362,1447],29679,3,0,5,9,74346507955914833,99186060470366289,595108686143727697),
(12,[4294,1188,1284,362,1449],29679,3,0,5,9,74346507955914833,99186060470366289,595108686143727697),
(11,[4294,1188,1284,394,1449,459],37871,3,0,5,9,74346507955914833,99115691726188625,595108686143727697),
(11,[4294,1188,1317,1410,423,362],54111,3,0,5,8,74346507859445857,324277947668383841,324611100380514401),
(12,[4294,1188,1317,1410,362],29663,3,0,5,9,74346507859445857,324277947668385889,324611100380516449),
(11,[4294,1188,1317,1254,1319,362],61791,3,0,4,7,99186060470366289,720665216765083745,109309480214279696),
(11,[4294,1188,1317,1254,362,1479],45919,3,0,8,10,180233461657976865,180251468308262945,148726270739428385),
(11,[4294,1188,1317,1286,1320,362],61663,3,0,4,7,99186060470366289,252290855518552161,109309480214279696),
(12,[4294,1188,1317,1286,362],29663,3,0,5,9,360307492011659361,252290855518552161,324611233524502625),
(11,[4294,1188,1317,1382,1319,327],61791,3,0,4,7,27058097891684369,594494058915905569,37181517432174096),
(12,[4294,1188,1317,1382,1319],30175,3,0,4,9,99186060470366289,648607622727155809,109309480214279696),
(11,[4294,1188,1317,1382,327,1481],45535,3,0,4,8,27058097891684369,252220487235747873,37181517432174096),
(12,[4294,1188,1317,1382,1320],30175,3,0,4,9,99186060470366289,252290855518552161,109309480214279696),
(11,[4294,1188,1317,1287,327,1320],63583,3,1,2,5,220749778174288902,360295395332739138,74316821141964996),
(11,[4294,1188,1317,1287,327,1449],55647,3,1,2,5,220749778174288902,360295395332739138,74316821141964996)]
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
theorem page15_ok : page15.all (replay raw target)=true := by decide +kernel
def pages : List (List Sample) := [page0,page1,page2,page3,page4,page5,page6,page7,page8,page9,page10,page11,page12,page13,page14,page15]
theorem allPages (p : List Sample) (hp : p∈pages) : p.all (replay raw target)=true := by
  simp only [pages,List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact page0_ok | exact page1_ok | exact page2_ok | exact page3_ok | exact page4_ok | exact page5_ok | exact page6_ok | exact page7_ok | exact page8_ok | exact page9_ok | exact page10_ok | exact page11_ok | exact page12_ok | exact page13_ok | exact page14_ok | exact page15_ok
theorem noCandidate (p : List Sample) (hp : p∈pages) (s : Sample) (hs : s∈p) :
    ∀ k, k ≤ s.1 → ¬ Live false target k (state raw s).toFinset :=
  replay_sound (List.all_eq_true.mp (allPages p hp) s hs)
end PEqualNP.Outside.L_meta_9822.Ranked

import PEqualNP.Defs

namespace Linear9798
set_option maxHeartbeats 0
inductive Port
  | bit
  | pair (a b : Port)
def Port.Val : Port → Type
  | .bit => Bool
  | .pair a b => a.Val × b.Val
def Port.dim : Port → Nat
  | .bit => 1
  | .pair a b => a.dim+b.dim
def Port.dot : (a : Port) → a.Val → a.Val → Bool
  | .bit,u,v => u && v
  | .pair a b,u,v => a.dot u.1 v.1 || b.dot u.2 v.2
inductive Net (X : Type) : Port → Port → Type
  | identity (a) : Net X a a
  | copy : Net X .bit (.pair .bit .bit)
  | add : Net X (.pair .bit .bit) .bit
  | scale (c : X → Bool) : Net X .bit .bit
  | swap (a b) : Net X (.pair a b) (.pair b a)
  | assoc (a b c) : Net X (.pair (.pair a b) c) (.pair a (.pair b c))
  | unassoc (a b c) : Net X (.pair a (.pair b c)) (.pair (.pair a b) c)
  | parallel {a b c d} (l : Net X a b) (r : Net X c d) : Net X (.pair a c) (.pair b d)
  | seq {a b c} (l : Net X a b) (r : Net X b c) : Net X a c

namespace Net
variable {X : Type}
def run {a b} (c : Net X a b) (x : X) : a.Val → b.Val := match c with
  | .identity _ => id
  | .copy => fun v => (v,v)
  | .add => fun v => v.1 || v.2
  | .scale t => fun v => t x && v
  | .swap _ _ => fun v => (v.2,v.1)
  | .assoc _ _ _ => fun v => (v.1.1,(v.1.2,v.2))
  | .unassoc _ _ _ => fun v => ((v.1,v.2.1),v.2.2)
  | .parallel l r => fun v => (l.run x v.1,r.run x v.2)
  | .seq l r => fun v => r.run x (l.run x v)
def rev {a b} (c : Net X a b) : Net X b a := match c with
  | .identity a => .identity a
  | .copy => .add
  | .add => .copy
  | .scale t => .scale t
  | .swap a b => .swap b a
  | .assoc a b c => .unassoc a b c
  | .unassoc a b c => .assoc a b c
  | .parallel l r => .parallel l.rev r.rev
  | .seq l r => .seq r.rev l.rev
def adds {a b} (c : Net X a b) : Nat := match c with
  | .add => 1
  | .parallel l r => l.adds+r.adds
  | .seq l r => l.adds+r.adds
  | _ => 0

theorem adjoint {a b} (c : Net X a b) (x : X) (u : a.Val) (v : b.Val) :
    b.dot (c.run x u) v = a.dot u (c.rev.run x v) := by
  induction c with
  | identity => rfl
  | copy => rcases v with ⟨i,j⟩; cases u <;> cases i <;> cases j <;> rfl
  | add => rcases u with ⟨i,j⟩; cases v <;> cases i <;> cases j <;> rfl
  | scale t => change (t x && u && v) = (u && (t x && v))
    cases h : t x <;> cases u <;> cases v <;> rfl
  | swap => simp [run,rev,Port.dot,Bool.or_comm]
  | assoc => simp [run,rev,Port.dot,Bool.or_assoc]
  | unassoc => simp [run,rev,Port.dot,Bool.or_assoc]
  | parallel l r li ri =>
    simp only [run,rev,Port.dot]
    rw [li,ri]
  | seq l r li ri =>
    simp only [run,rev]
    rw [ri,li]

theorem balance {a b} (c : Net X a b) :
    c.rev.adds+a.dim=c.adds+b.dim := by
  induction c with
  | identity => rfl
  | copy => rfl
  | add => rfl
  | scale => rfl
  | swap => simp [rev,adds,Port.dim,Nat.add_comm]
  | assoc => simp [rev,adds,Port.dim,Nat.add_assoc]
  | unassoc => simp [rev,adds,Port.dim,Nat.add_assoc]
  | parallel l r li ri =>
    simp only [rev,adds,Port.dim]
    omega
  | seq l r li ri =>
    simp only [rev,adds]
    omega

end Net
end Linear9798
namespace Lines9798
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 10000
abbrev P := Fin 19
abbrev Q := Fin 21
abbrev F := Fin 95
abbrev X := Q → Bool
abbrev Signal := X → Bool
def row : F → P := ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18]
def col : F → Q := ![2, 3, 6, 16, 18, 3, 4, 7, 17, 19, 4, 5, 8, 18, 20, 0, 5, 6, 9, 19, 1, 6, 7, 10, 20, 0, 2, 7, 8, 11, 1, 3, 8, 9, 12, 2, 4, 9, 10, 13, 3, 5, 10, 11, 14, 4, 6, 11, 12, 15, 5, 7, 12, 13, 16, 6, 8, 13, 14, 17, 7, 9, 14, 15, 18, 8, 10, 15, 16, 19, 9, 11, 16, 17, 20, 0, 10, 12, 17, 18, 1, 11, 13, 18, 19, 2, 12, 14, 19, 20, 0, 3, 13, 15, 20]
def ng : P → Nat := ![327756, 655512, 1311024, 524897, 1049794, 2437, 4874, 9748, 19496, 38992, 77984, 155968, 311936, 623872, 1247744, 398337, 796674, 1593348, 1089545]

def has (p : P) (q : Q) := (ng p).testBit q.val
def out (p : P) : X := fun j => !(has p j)
def one (q : Q) : X := fun j => decide (j=q)
def fires (v : Signal) (i : F) := v (one (col i)) = true ∧ v (out (row i)) = false
def mono (v : Signal) := ∀ x y : X,(∀ q,x q=true → y q=true) → v x=true → v y=true
def raw (q : Q) : Signal := fun x => x q
def meet (u v : Signal) : Signal := fun x => u x && v x
def join (u v : Signal) : Signal := fun x => u x || v x
theorem flags : ∀ (i j : F),row i=row j → col i=col j → i=j := by decide +kernel
theorem edgeHere : ∀ i : F, has (row i) (col i)=true := by decide +kernel
theorem common : ∀ (p q : P) (a b : Q),has p a=true → has p b=true → has q a=true → has q b=true → a≠b → p=q := by decide +kernel

theorem forced {v : Signal} (m : mono v) {i : F} (hi : fires v i) {r : P}
    (off : v (out r)=false) : has r (col i)=true := by
  by_contra ne
  have ex : out r (col i)=true := by simpa [out] using ne
  have sub : ∀ q,one (col i) q=true → out r q=true := by
    intro q eq
    have qeq : q=col i := by simpa [one] using eq
    simpa [qeq] using ex
  have yes := m _ _ sub hi.1
  rw [off] at yes
  contradiction

def uniform (c : F → F) (v : Signal) :=
  ∀ i j,row i=row j → fires v i → fires v j → c i=c j

theorem uniqueRow {v : Signal} (m : mono v) {i j a b : F}
    (ij : row i=row j) (ab : row a=row b) (hij : i≠j) (hab : a≠b)
    (fi : fires v i) (fj : fires v j) (fa : fires v a) (fb : fires v b) : row i=row a := by
  have dif : col i ≠ col j := fun e => hij (flags i j ij e)
  exact common _ _ _ _ (edgeHere i) (by simpa only [ij] using edgeHere j)
    (forced m fi fa.2) (forced m fj fa.2) dif

def palette (c : F → F) : Finset F := univ.image c
theorem recolorCost (c : F → F) (a b : F) :
    (palette c).card ≤ (palette (fun i => if c i=b then a else c i)).card+1 := by
  classical
  let newColor := fun i => if c i=b then a else c i
  have sub : (palette c).erase b ⊆ palette newColor := by
    intro w hw
    obtain ⟨ne,wp⟩ := mem_erase.mp hw
    obtain ⟨i,_,rfl⟩ := mem_image.mp wp
    exact mem_image.mpr ⟨i,mem_univ i,by simp [newColor,ne]⟩
  have le := card_le_card sub
  by_cases h : b∈palette c
  · have er := card_erase_add_one h
    change (palette c).card ≤ (palette newColor).card+1
    omega
  · rw [erase_eq_of_notMem h] at le
    exact Nat.le.step le

theorem chooseColors (c : F → F) (u v : Signal) (good : mono (join u v))
    (uu : uniform c u) (vv : uniform c v) :
    ∃ c' : F → F, uniform c' (join u v) ∧
        (∀ a b,c a=c b → c' a=c' b) ∧ (palette c).card≤(palette c').card+1 := by
  classical
  by_cases old : uniform c (join u v)
  · exact ⟨c,old,fun _ _ eq=>eq,Nat.le_succ _⟩
  unfold uniform at old
  push_neg at old
  obtain ⟨i,j,ij,fi,fj,ne⟩ := old
  have split (a : F) (fa : fires (join u v) a) : fires u a ∨ fires v a := by
    rcases fa with ⟨p,n⟩
    have pos : u (one (col a))=true ∨ v (one (col a))=true := by simpa [join] using p
    have neg : u (out (row a))=false ∧ v (out (row a))=false := by simpa [join] using n
    exact pos.elim (fun h => Or.inl ⟨h,neg.1⟩) (fun h => Or.inr ⟨h,neg.2⟩)
  have dich (a : F) (ar : row a=row i) (here : fires (join u v) a) : c a=c i ∨ c a=c j := by
    rcases split i fi with iu|iv <;> rcases split j fj with ju|jv
    · exact False.elim (ne (uu i j ij iu ju))
    · exact (split a here).elim (fun h=>Or.inl (uu a i ar h iu)) (fun h=>Or.inr (vv a j (ar.trans ij) h jv))
    · exact (split a here).elim (fun h=>Or.inr (uu a j (ar.trans ij) h ju)) (fun h=>Or.inl (vv a i ar h iv))
    · exact False.elim (ne (vv i j ij iv jv))
  let k := fun a : F => if c a=c j then c i else c a
  refine ⟨k,?_,?_,recolorCost c (c i) (c j)⟩
  · intro a b ab fa fb
    by_cases eq : a=b
    · rw [eq]
    have ar : row a=row i := (uniqueRow good ij ab (fun e=>ne (congrArg c e)) eq fi fj fa fb).symm
    have collapse (a : F) (z : c a=c i ∨ c a=c j) : k a=c i := by
      rcases z with z|z <;> simp [k,z]
    exact (collapse a (dich a ar fa)).trans (collapse b (dich b (ab.symm.trans ar) fb)).symm
  · intro a b eq
    simp only [k,eq]

inductive Built : List Signal → Nat → Prop
  | start : Built ((fun _ => true) :: List.ofFn raw) 0
  | addAnd {bank n} (old : Built bank n) {u v} (hu : u∈bank) (hv : v∈bank) :
      Built (meet u v :: bank) n
  | addOr {bank n} (old : Built bank n) {u v} (hu : u∈bank) (hv : v∈bank) :
      Built (join u v :: bank) (n+1)

theorem account {bank n} (built : Built bank n) :
    (∀ v∈bank,mono v) ∧ ∃ c : F→F,(∀ v∈bank,uniform c v) ∧ 95≤(palette c).card+n := by
  induction built with
  | start =>
    constructor
    · intro v h
      rcases List.mem_cons.mp h with e|h
      · subst v
        intro _ _ _ _
        rfl
      obtain ⟨q,rfl⟩ := List.mem_ofFn.mp h
      intro x y le val
      exact le q val
    · refine ⟨id,?_,by simp [palette]⟩
      intro v hv
      rcases List.mem_cons.mp hv with e|hv
      · subst v
        intro i j _ fi _
        have bad : true = false := fi.2
        contradiction
      obtain ⟨q,rfl⟩ := List.mem_ofFn.mp hv
      intro i j r fi fj
      have a : q=col i := by simpa [raw,one] using fi.1
      have b : q=col j := by simpa [raw,one] using fj.1
      exact flags i j r (a.symm.trans b)
  | @addAnd bank n prev u v hu hv ih =>
    obtain ⟨mons,c,valid,num⟩ := ih
    have mg : mono (meet u v) := by
      intro x y le z
      have p : u x=true ∧ v x=true := by simpa [meet] using z
      simp [meet,mons u hu x y le p.1,mons v hv x y le p.2]
    refine ⟨fun w hw => (List.mem_cons.mp hw).elim (fun eq => by simpa only [eq] using mg) (mons w),c,?_,num⟩
    intro w hw
    rcases List.mem_cons.mp hw with eq|old
    · subst w
      intro i j same fi fj
      have pi : u (one (col i))=true ∧ v (one (col i))=true := by simpa [meet] using fi.1
      have pj : u (one (col j))=true ∧ v (one (col j))=true := by simpa [meet] using fj.1
      have bad : u (out (row i))=false ∨ v (out (row i))=false := by
        cases h : u (out (row i)) with
        | false => exact Or.inl rfl
        | true => exact Or.inr (by simpa [meet,h] using fi.2)
      rcases bad with bad|bad
      · exact valid u hu i j same ⟨pi.1,bad⟩ ⟨pj.1,by simpa only [← same] using bad⟩
      · exact valid v hv i j same ⟨pi.2,bad⟩ ⟨pj.2,by simpa only [← same] using bad⟩
    · exact valid w old
  | @addOr bank n prev u v hu hv ih =>
    obtain ⟨mons,c,valid,num⟩ := ih
    have mg : mono (join u v) := by
      intro x y le z
      have p : u x=true ∨ v x=true := by simpa [join] using z
      rcases p with h|h
      · simp [join,mons u hu x y le h]
      · simp [join,mons v hv x y le h]
    obtain ⟨d,fresh,less,count⟩ := chooseColors c u v mg (valid u hu) (valid v hv)
    refine ⟨fun w hw => (List.mem_cons.mp hw).elim (fun eq => by simpa only [eq] using mg) (mons w),d,?_,by omega⟩
    intro w hw
    rcases List.mem_cons.mp hw with eq|old
    · simpa only [eq] using fresh
    · intro i j r a b
      exact less i j (valid w old i j r a b)

theorem atLeast76 {bank n} (built : Built bank n) (outputs : P → Signal)
    (avail : ∀ p,outputs p∈bank)
    (correct : ∀ i : F,fires (outputs (row i)) i) : 76≤n := by
  classical
  obtain ⟨_,c,uniforms,le⟩ := account built
  let pick : P → F := fun p => if a : ∃ i : F,row i=p then Classical.choose a else 0
  have repr (i : F) : row (pick (row i))=row i := by
    have a : ∃ j : F,row j=row i := ⟨i,rfl⟩
    simp only [pick,dif_pos a]
    exact Classical.choose_spec a
  have sub : palette c ⊆ univ.image (fun p => c (pick p)) := by
    intro q hq
    obtain ⟨i,_,rfl⟩ := mem_image.mp hq
    let j := pick (row i)
    have same : row j=row i := repr i
    refine mem_image.mpr ⟨row i,mem_univ _,?_⟩
    exact uniforms _ (avail (row i)) j i same (by simpa only [same] using correct j) (correct i)
  have a := card_le_card sub
  have b : (univ.image (fun p : P=>c (pick p))).card ≤ (univ : Finset P).card := Finset.card_image_le
  simp only [card_univ,Fintype.card_fin] at b
  omega


end Lines9798
namespace Lines9798
open Linear9798
namespace AdjointBank

def Bundle : Port → Type
  | .bit => Signal
  | .pair a b => Bundle a × Bundle b
def atX : (a : Port) → Bundle a → X → a.Val
  | .bit,v,x => v x
  | .pair a b,v,x => (atX a v.1 x,atX b v.2 x)
def Available : (a : Port) → Bundle a → List Signal → Prop
  | .bit,v,bank => v∈bank
  | .pair a b,v,bank => Available a v.1 bank ∧ Available b v.2 bank

theorem available_more {a : Port} {v : Bundle a} {s t : List Signal}
    (sub : ∀ w∈s,w∈t) (h : Available a v s) : Available a v t := by
  induction a with
  | bit => exact sub _ h
  | pair a b l r => exact ⟨l h.1,r h.2⟩

def liftNet {a b} (c : Net X a b) : Bundle a → Bundle b := match c with
  | .identity _ => id
  | .copy => fun v => (v,v)
  | .add => fun v => join v.1 v.2
  | .scale t => fun v => meet t v
  | .swap _ _ => fun v => (v.2,v.1)
  | .assoc _ _ _ => fun v => (v.1.1,(v.1.2,v.2))
  | .unassoc _ _ _ => fun v => ((v.1,v.2.1),v.2.2)
  | .parallel l r => fun v => (liftNet l v.1,liftNet r v.2)
  | .seq l r => fun v => liftNet r (liftNet l v)

theorem evaluate {a b} (c : Net X a b) (v : Bundle a) (x : X) :
    atX b (liftNet c v) x = c.run x (atX a v x) := by
  induction c with
  | parallel l r li ri => simp only [atX,liftNet,Net.run,li,ri]
  | seq l r li ri => simp only [atX,liftNet,Net.run,li,ri]
  | _ => rfl

def supplied {a b} (c : Net X a b) (bank : List Signal) : Prop := match c with
  | .scale t => t∈bank
  | .parallel l r => supplied l bank ∧ supplied r bank
  | .seq l r => supplied l bank ∧ supplied r bank
  | _ => True

theorem supplied_more {a b} (c : Net X a b) {s t : List Signal}
    (sub : ∀ w∈s,w∈t) (h : supplied c s) : supplied c t := by
  induction c with
  | scale u => exact sub _ h
  | parallel l r li ri => exact ⟨li h.1,ri h.2⟩
  | seq l r li ri => exact ⟨li h.1,ri h.2⟩
  | _ => trivial

theorem supplied_rev {a b} (c : Net X a b) (s : List Signal)
    (h : supplied c s) : supplied c.rev s := by
  induction c with
  | scale => exact h
  | parallel l r li ri => exact ⟨li h.1,ri h.2⟩
  | seq l r li ri => exact ⟨ri h.2,li h.1⟩
  | _ => trivial

theorem build {a b} (c : Net X a b) {bank n} (base : Built bank n)
    (ctrl : supplied c bank) (v : Bundle a) (av : Available a v bank) :
    ∃ t, Built t (n+c.adds) ∧ (∀ w∈bank,w∈t) ∧ Available b (liftNet c v) t := by
  induction c generalizing bank n with
  | identity => exact ⟨bank,base,fun _ h=>h,av⟩
  | copy => exact ⟨bank,base,fun _ h=>h,av,av⟩
  | swap => exact ⟨bank,base,fun _ h=>h,av.2,av.1⟩
  | assoc => exact ⟨bank,base,fun _ h=>h,av.1.1,av.1.2,av.2⟩
  | unassoc => exact ⟨bank,base,fun _ h=>h,⟨av.1,av.2.1⟩,av.2.2⟩
  | add =>
    refine ⟨_,Built.addOr base av.1 av.2,fun _ h=>List.mem_cons_of_mem _ h,?_⟩
    exact List.mem_cons_self
  | scale u =>
    refine ⟨_,Built.addAnd base ctrl av,fun _ h=>List.mem_cons_of_mem _ h,?_⟩
    exact List.mem_cons_self
  | parallel l r li ri =>
    obtain ⟨s,bs,ss,al⟩ := li base ctrl.1 v.1 av.1
    obtain ⟨t,bt,st,ar⟩ := ri bs (supplied_more r ss ctrl.2) v.2 (available_more ss av.2)
    refine ⟨t,?_,fun w h=>st w (ss w h),available_more st al,ar⟩
    simpa only [Net.adds,Nat.add_assoc] using bt
  | seq l r li ri =>
    obtain ⟨s,bs,ss,al⟩ := li base ctrl.1 v av
    obtain ⟨t,bt,st,ar⟩ := ri bs (supplied_more r ss ctrl.2) _ al
    refine ⟨t,?_,fun w h=>st w (ss w h),ar⟩
    simpa only [Net.adds,Nat.add_assoc] using bt

inductive Leaf : Port → Type
  | bit : Leaf .bit
  | left {a b} : Leaf a → Leaf (.pair a b)
  | right {a b} : Leaf b → Leaf (.pair a b)
def zero : (a : Port) → a.Val
  | .bit => false
  | .pair a b => (zero a,zero b)
def select {a} : Leaf a → a.Val
  | .bit => true
  | .left p => (select p,zero _)
  | .right p => (zero _,select p)
def read {a} : Leaf a → a.Val → Bool
  | .bit,v => v
  | .left p,v => read p v.1
  | .right p,v => read p v.2
def signal {a} : Leaf a → Bundle a → Signal
  | .bit,v => v
  | .left p,v => signal p v.1
  | .right p,v => signal p v.2

theorem zero_dot (a : Port) (v : a.Val) : a.dot (zero a) v = false := by
  induction a with
  | bit => rfl
  | pair a b l r => simp [Port.dot,zero,l,r]
theorem select_dot {a} (p : Leaf a) (v : a.Val) :
    a.dot (select p) v = read p v := by
  induction p with
  | bit => simp [Port.dot,select,read]
  | left p ih => simp [Port.dot,select,read,zero_dot,ih]
  | right p ih => simp [Port.dot,select,read,zero_dot,ih]
theorem signal_works {a} (p : Leaf a) (v : Bundle a) (x : X) :
    signal p v x = read p (atX a v x) := by
  induction p with
  | bit => rfl
  | left p ih => exact ih _
  | right p ih => exact ih _
theorem signal_available {a} (p : Leaf a) (v : Bundle a) {s} (h : Available a v s) :
    signal p v ∈ s := by
  induction p with
  | bit => exact h
  | left p ih => exact ih _ h.1
  | right p ih => exact ih _ h.2

theorem ninetyFourORs {a} (c : Net X a .bit) (pins : P → Leaf a) (width : a.dim=19)
    {bank n} (base : Built bank n) (ctrl : supplied c bank) (unit : (fun _ => true) ∈ bank)
    (on : ∀ i : F,c.run (one (col i)) (select (pins (row i)))=true)
    (off : ∀ i : F,c.run (out (row i)) (select (pins (row i)))=false) : 94≤n+c.adds := by
  let w : Bundle a := liftNet c.rev (fun _ => true)
  obtain ⟨s,bs,_,av⟩ := build c.rev base (supplied_rev c bank ctrl) (fun _=>true) unit
  have value (p : P) (x : X) : signal (pins p) w x = c.run x (select (pins p)) := by
    rw [signal_works]
    have v := evaluate c.rev (fun _ => true) x
    change read (pins p) (atX a (liftNet c.rev (fun _ => true)) x) = _
    rw [v]
    have h := c.adjoint x (select (pins p)) true
    simpa only [Port.dot,Bool.and_true,select_dot,atX] using h.symm
  have lower := atLeast76 bs (fun p=>signal (pins p) w)
    (fun p=>signal_available (pins p) w av)
    (fun i=>⟨(value _ _).trans (on i),(value _ _).trans (off i)⟩)
  have count := c.balance
  simp only [Port.dim,width] at count
  omega
end AdjointBank
end Lines9798

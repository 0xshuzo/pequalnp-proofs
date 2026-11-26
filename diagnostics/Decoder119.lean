import PEqualNP.Defs

namespace Lines9740
open Finset
set_option maxHeartbeats 0
set_option maxRecDepth 10000
abbrev P := Fin 20
abbrev Q := Fin 21
abbrev F := Fin 100
abbrev X := Q → Bool
abbrev Signal := X → Bool
def row : F → P := ![0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 6, 6, 6, 6, 6, 7, 7, 7, 7, 7, 8, 8, 8, 8, 8, 9, 9, 9, 9, 9, 10, 10, 10, 10, 10, 11, 11, 11, 11, 11, 12, 12, 12, 12, 12, 13, 13, 13, 13, 13, 14, 14, 14, 14, 14, 15, 15, 15, 15, 15, 16, 16, 16, 16, 16, 17, 17, 17, 17, 17, 18, 18, 18, 18, 18, 19, 19, 19, 19, 19]
def col : F → Q := ![1, 2, 5, 15, 17, 2, 3, 6, 16, 18, 3, 4, 7, 17, 19, 4, 5, 8, 18, 20, 0, 5, 6, 9, 19, 1, 6, 7, 10, 20, 0, 2, 7, 8, 11, 1, 3, 8, 9, 12, 2, 4, 9, 10, 13, 3, 5, 10, 11, 14, 4, 6, 11, 12, 15, 5, 7, 12, 13, 16, 6, 8, 13, 14, 17, 7, 9, 14, 15, 18, 8, 10, 15, 16, 19, 9, 11, 16, 17, 20, 0, 10, 12, 17, 18, 1, 11, 13, 18, 19, 2, 12, 14, 19, 20, 0, 3, 13, 15, 20]
def ng : P → Nat := ![163878, 327756, 655512, 1311024, 524897, 1049794, 2437, 4874, 9748, 19496, 38992, 77984, 155968, 311936, 623872, 1247744, 398337, 796674, 1593348, 1089545]

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
    (∀ v∈bank,mono v) ∧ ∃ c : F→F,(∀ v∈bank,uniform c v) ∧ 100≤(palette c).card+n := by
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
        exact False.elim ((by decide : true ≠ false) bad)
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

theorem atLeast80 {bank n} (built : Built bank n) (outputs : P → Signal)
    (avail : ∀ p,outputs p∈bank)
    (correct : ∀ i : F,fires (outputs (row i)) i) : 80≤n := by
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


def pt (i : P) : Q := ⟨i.val+1,by have := i.isLt; omega⟩
theorem selfHit : ∀ i : P,has i (pt i)=true := by decide +kernel
theorem cross : ∀ i j : P,has i (pt j)=true → has j (pt i)=true → i=j := by decide +kernel


def rank : P → Nat := ![1, 2, 1, 1, 0, 1, 0, 2, 2, 1, 2, 1, 1, 1, 2, 1, 0, 2, 1, 0]
def via : P → Q := ![17, 3, 17, 20, 0, 20, 0, 1, 4, 5, 4, 5, 17, 7, 10, 17, 0, 1, 20, 0]

theorem paths : ∀ i : P, has i (via i)=true ∧ via i ≠ pt i ∧
    ∀ j, pt j = via i → rank j < rank i := by decide +kernel

theorem incident {w : Signal} (m : mono w) {p : P} {q : Q}
    (a : w (one q)=true) (b : w (out p)=false) : has p q=true := by
  by_contra ne
  have no : out p q=true := by simpa [out] using ne
  have yes := m _ _ (fun j hj => by
    have e : j=q := by simpa [one] using hj
    simpa only [e] using no) a
  rw [b] at yes
  contradiction

def separates (b : P → Signal) := ∀ i q, has i q = true →
  ∃ j, b j (one q)=true ∧ b j (out i)=false

def OrRow (i : P) (x : X) : Prop := ∃ q, has i q = true ∧ x q = true

theorem decoderSeparates {b : P → Signal} (read : P → (P → Bool) → Bool)
    (up : ∀ i u v, (∀ a, u a=true → v a=true) → read i u=true → read i v=true)
    (correct : ∀ i x, read i (fun j => b j x)=true ↔ OrRow i x) : separates b := by
  classical
  intro i q edge
  by_contra bad
  have sub : ∀ a, b a (one q)=true → b a (out i)=true := by
    intro a oneOn
    cases ho : b a (out i) with
    | false => exact False.elim (bad ⟨a,oneOn,ho⟩)
    | true => rfl
  have hit := (correct i (one q)).mpr ⟨q,edge,by simp [one]⟩
  obtain ⟨j,hj,ox⟩ := (correct i (out i)).mp (up i _ _ sub hit)
  simp [out,hj] at ox

theorem shape {b : P → Signal} (m : ∀ j,mono (b j)) (h : separates b) :
    ∃ f : P ≃ P, ∀ i x, b (f i) x = true ↔ OrRow i x := by
  classical
  choose f fOn fOff using fun i => h i (pt i) (selfHit i)
  have inj : Function.Injective f := by
    intro i j e
    apply cross i j
    · exact incident (m (f i)) (by simpa only [e] using fOn j) (fOff i)
    · exact incident (m (f j)) (by simpa only [←e] using fOn i) (fOff j)
  have surj : Function.Surjective f := Finite.injective_iff_surjective.mp inj
  let Private (i : P) := ∀ r, b (f i) (out r)=false → i=r
  have step (d : Nat) : ∀ i,rank i<d → Private i := by
    induction d with
    | zero => intro i e; omega
    | succ d ih =>
      intro i small
      obtain ⟨edge,diff,older⟩ := paths i
      obtain ⟨t,on,off⟩ := h i (via i) edge
      obtain ⟨j,rfl⟩ := surj t
      have eq : j=i := by
        by_cases same : pt j=via i
        · have pr : Private j := ih j (by have := older j same; omega)
          exact pr i off
        · exact common j i (pt j) (via i) (selfHit j)
            (incident (m _) on (fOff j)) (incident (m _) (fOn j) off) edge same
      subst j
      intro r neg
      exact common i r (via i) (pt i) edge (selfHit i)
        (incident (m _) on neg) (incident (m _) (fOn i) neg) diff
  refine ⟨Equiv.ofBijective f ⟨inj,surj⟩,?_⟩
  intro i x
  change b (f i) x=true ↔ OrRow i x
  constructor
  · intro yes
    by_contra absent
    have sub : ∀ q, x q=true → out i q=true := by
      intro q xq
      have no : has i q ≠ true := fun e => absent ⟨q,e,xq⟩
      simpa [out] using no
    have z := m _ _ _ sub yes
    rw [fOff i] at z
    contradiction
  · rintro ⟨q,edge,xq⟩
    obtain ⟨t,on,off⟩ := h i q edge
    obtain ⟨j,rfl⟩ := surj t
    have eq : j=i := step (rank j+1) j (by omega) i off
    subst j
    apply m _ _ _ _ on
    intro s hs
    have eq : s=q := by simpa [one] using hs
    simpa only [eq] using xq

theorem cut80 {bank n} (built : Built bank n) (b : P → Signal) (avail : ∀ j, b j ∈ bank)
    (read : P → (P → Bool) → Bool)
    (up : ∀ i u v, (∀ a, u a=true → v a=true) → read i u=true → read i v=true)
    (correct : ∀ i x, read i (fun j => b j x)=true ↔ OrRow i x) : 80≤n := by
  obtain ⟨m,_⟩ := account built
  obtain ⟨f,law⟩ := shape (fun j=>m _ (avail j)) (decoderSeparates read up correct)
  apply atLeast80 built (fun i=>b (f i)) (fun i=>avail _)
  intro e
  constructor
  · exact (law _ _).mpr ⟨col e,edgeHere e,by simp [one]⟩
  · cases h : b (f (row e)) (out (row e)) with
    | false => rfl
    | true =>
      obtain ⟨q,edge,ox⟩ := (law _ _).mp h
      simp [out,edge] at ox


namespace Decoder
abbrev K := P ⊕ P
abbrev Y := X × (P → Bool)
abbrev W := Y → Bool
def allP : X := fun _ => true
def pin (i : P) : P → Bool := fun j=>decide (j=i)
def hi : K → Y
  | .inl i | .inr i => (allP,pin i)
def lo : K → Y
  | .inl i => (out i,pin i)
  | .inr _ => (allP,fun _=>false)
def observes (w : W) (k : K) := w (hi k) ≠ w (lo k)
def agrees (c : K → K) (w : W) := ∀ i j, observes w i → observes w j → c i=c j
def input (b : P → Signal) : K → W
  | .inl i => fun y=> b i y.1
  | .inr i => fun y=> y.2 i
def target (y : Y) : Prop := ∃ i, y.2 i=true ∧ OrRow i y.1

def binary (op : Bool→Bool→Bool) (a b : W) : W := fun y=>op (a y) (b y)
inductive Suffix (inputs : K→W) : List W → Nat → Prop
  | start : Suffix inputs (List.ofFn (fun i : P => inputs (.inl i)) ++ List.ofFn (fun i : P => inputs (.inr i))) 0
  | add {bank n u v} (old : Suffix inputs bank n) (a : u ∈ bank) (b : v ∈ bank)
      (op : Bool→Bool→Bool) : Suffix inputs (binary op u v :: bank) (n+1)

def palette (c : K → K) : Finset K := univ.image c
theorem recolorCost (c : K → K) (a b : K) :
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


theorem merge (c : K→K) {u v : W} (a : agrees c u) (b : agrees c v)
    (op : Bool→Bool→Bool) : ∃ e : K→K, agrees e (binary op u v) ∧
    (∀ i j,c i=c j → e i=e j) ∧ (palette c).card ≤ (palette e).card+1 := by
  classical
  let pick (w : W) : K := if z : ∃ i, observes w i then z.choose else .inl 0
  have one {w : W} (h : agrees c w) {i} (z : observes w i) : c i=c (pick w) := by
    have ex : ∃ j, observes w j := ⟨i,z⟩
    simpa only [pick,dif_pos ex] using h i ex.choose z ex.choose_spec
  let e (i : K) := if c i=c (pick v) then c (pick u) else c i
  have both (i : K) (z : observes (binary op u v) i) : e i=c (pick u) := by
    by_cases yes : observes u i
    · simp [e,one a yes]
    · have eq : u (hi i)=u (lo i) := Classical.not_not.mp yes
      have other : observes v i := by
        intro same
        apply z
        simp only [binary,eq,same]
      simp [e,one b other]
  exact ⟨e,fun i j ai aj=>(both i ai).trans (both j aj).symm,
    fun i j eq=>by simp only [e,eq],recolorCost c _ _⟩

theorem budget {ins : K→W} (init : ∀ k,agrees id (ins k)) {bank n}
    (s : Suffix ins bank n) : ∃ c : K→K, (∀ w∈bank,agrees c w) ∧ 40≤(palette c).card+n := by
  induction s with
  | start =>
    refine ⟨id,?_,?_⟩
    · intro w hw
      rcases List.mem_append.mp hw with left|right
      · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp left
        exact init (.inl i)
      · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp right
        exact init (.inr i)
    · simp [palette,K,P]
  | add old hu hv op ih =>
    obtain ⟨c,valid,h⟩ := ih
    obtain ⟨e,gate,coarse,cost⟩ := merge c (valid _ hu) (valid _ hv) op
    refine ⟨e,?_,by omega⟩
    intro w hw
    rcases List.mem_cons.mp hw with rfl|hw
    · exact gate
    · exact fun i j ai aj=>coarse _ _ (valid w hw i j ai aj)

theorem rowsApart : ∀ i j : P, i≠j → ∃ q : Q,has i q=true ∧ has j q=false := by decide +kernel

theorem initial {b : P→Signal} (f : P ≃ P)
    (law : ∀ i x, b (f i) x=true ↔ OrRow i x) : ∀ k,agrees id (input b k) := by
  have on (i : P) : b (f i) allP=true := (law _ _).mpr ⟨_,selfHit i,rfl⟩
  have on' {i j : P} (ne : i≠j) : b (f i) (out j)=true := by
    obtain ⟨q,h,qj⟩ := rowsApart i j ne
    exact (law _ _).mpr ⟨_,h,by simp [out,qj]⟩
  intro k
  have onlyIn (i : P) (j : K) (h : observes (input b (.inl (f i))) j) : j=Sum.inl i := by
    cases j with
    | inr j => exact False.elim (h rfl)
    | inl j =>
      by_contra ne
      have neq : i≠j := by rintro rfl; exact ne rfl
      exact h ((on i).trans (on' neq).symm)
  have onlyRaw (i : P) (j : K) (h : observes (input b (.inr i)) j) : j=Sum.inr i := by
    cases j with
    | inl j => exact False.elim (h rfl)
    | inr j =>
      by_contra ne
      have neq : i≠j := by rintro rfl; exact ne rfl
      apply h
      simp [input,hi,lo,pin,neq]
  cases k with
  | inl k =>
    obtain ⟨i,rfl⟩ := f.surjective k
    exact fun a b ha hb=>(onlyIn i a ha).trans (onlyIn i b hb).symm
  | inr k => exact fun a b ha hb=>(onlyRaw k a ha).trans (onlyRaw k b hb).symm

theorem endObserves {w : W} (ok : ∀ y,w y=true ↔ target y) : ∀ k, observes w k := by
  have on (i : P) : w (allP,pin i)=true :=
    (ok _).mpr ⟨i,by simp [pin],pt i,selfHit i,rfl⟩
  intro k eq
  cases k with
  | inr i =>
    have h := on i
    change w (allP,pin i)=w (allP,fun _=>false) at eq
    rw [eq] at h
    obtain ⟨_,bad,_⟩ := (ok _).mp h
    contradiction
  | inl i =>
    have h := on i
    change w (allP,pin i)=w (out i,pin i) at eq
    rw [eq] at h
    obtain ⟨j,pj,q,edge,ox⟩ := (ok _).mp h
    have e : j=i := by simpa [pin] using pj
    subst j
    simp [out,edge] at ox

theorem cost39 {b : P→Signal} (f : P ≃ P) (law : ∀ i x, b (f i) x=true ↔ OrRow i x)
    {bank n} (s : Suffix (input b) bank n) {w} (hw : w∈bank) (ok : ∀ y,w y=true ↔ target y) :
    39≤n := by
  classical
  obtain ⟨c,valid,bound⟩ := budget (initial f law) s
  have eq (i : K) : c i=c (.inl 0) := valid w hw _ _ (endObserves ok i) (endObserves ok _)
  have sub : palette c ⊆ {c (.inl 0)} := by
    intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    simpa only [Finset.mem_singleton] using eq i
  have le := Finset.card_le_card sub
  simp only [Finset.card_singleton] at le
  omega

theorem interface119 {bank n} (built : Built bank n) (b : P → Signal) (avail : ∀ j, b j ∈ bank)
    (read : P → (P → Bool) → Bool)
    (up : ∀ i u v, (∀ a, u a=true → v a=true) → read i u=true → read i v=true)
    (correct : ∀ i x, read i (fun j => b j x)=true ↔ OrRow i x)
    {outBank k} (s : Suffix (input b) outBank k) {w} (hw : w ∈ outBank)
    (ok : ∀ y,w y=true ↔ target y) : 119≤n+k := by
  obtain ⟨m,_⟩ := account built
  obtain ⟨f,law⟩ := shape (fun j=>m _ (avail j)) (decoderSeparates read up correct)
  have a := cut80 built b avail read up correct
  have e := cost39 f law s hw ok
  omega
end Decoder
end Lines9740

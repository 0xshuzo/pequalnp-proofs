import PEqualNP.Defs
namespace PEqualNP.Outside.L_pcx_177.Colors
open PEqualNP.ProofComplexity
theorem snd_res {V : Type} [DecidableEq V] {C D R : LinClause V} (h : IsLinResolvent C D R) (a : V → Bool) (hR : ¬ LinClauseSat a R) :
    ¬ LinClauseSat a C ∨ ¬ LinClauseSat a D := by
  obtain ⟨f, hC, hD, rfl⟩ := h
  by_cases hf : Odd (f.filter (fun v => a v = true)).card
  · left
    rintro ⟨q, hq, hs⟩
    refine hR ⟨q, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨?_, hq⟩), hs⟩
    rintro rfl
    have := hs.1 hf
    cases this
  · right
    rintro ⟨q, hq, hs⟩
    refine hR ⟨q, Finset.mem_union_right _ (Finset.mem_erase.2 ⟨?_, hq⟩), hs⟩
    rintro rfl
    exact hf (hs.2 rfl)


section
variable {V : Type} [DecidableEq V]
theorem card_step (N Q : Finset (LinClause V)) (R : LinClause V) (hR : R ∈ N) : (N.erase R ∪ Q).card + 1 ≤ N.card + Q.card := by
  have h1 := Finset.card_union_le (N.erase R) Q
  have h2 := Finset.card_erase_of_mem hR
  have h3 := Finset.card_pos.2 ⟨R, hR⟩
  omega

theorem tl {N : Finset (LinClause V)} {R : LinClause V} {π : List (LinClause V)} (h : ∀ M ∈ N, M ∈ R :: π) : ∀ M ∈ N.erase R, M ∈ π := by
  intro M hM
  obtain ⟨h1, h2⟩ := Finset.mem_erase.1 hM
  rcases List.mem_cons.1 (h M h2) with e | e
  · exact absurd e h1
  · exact e

theorem tln {N : Finset (LinClause V)} {R : LinClause V} {π : List (LinClause V)} (h : ∀ M ∈ N, M ∈ R :: π) (hR : R ∉ N) : ∀ M ∈ N, M ∈ π := by
  intro M hM
  rcases List.mem_cons.1 (h M hM) with e | e
  · subst e; exact absurd hM hR
  · exact e


end

section
variable {V : Type} [DecidableEq V]
inductive Paid (initial : List (LinClause V)) : Nat → List (LinClause V) → Prop
  | start : Paid initial 0 initial
  | res {π n A B C} : Paid initial n π → A∈π → B∈π → IsLinResolvent A B C → Paid initial (n+1) (C::π)
  | weak {π n A B} : Paid initial n π → A∈π → (∀x,LinClauseSat x A → LinClauseSat x B) → Paid initial n (B::π)

theorem tailPrice {k n : Nat} {initial π : List (LinClause V)} (w : Fin k → V → Bool)
    (privateRow : ∀ A∈initial,∀i j,¬LinClauseSat (w i) A → ¬LinClauseSat (w j) A → i=j)
    (h : Paid initial n π) (N : Finset (LinClause V)) (available : ∀C∈N,C∈π)
    (hits : ∀i, ∃C∈N,¬LinClauseSat (w i) C) : k ≤ n+N.card := by
  classical
  induction h generalizing N with
  | start =>
    choose f inside no using hits
    have inj : Function.Injective f := by
      intro a b e
      exact privateRow _ (available _ (inside a)) a b (no a) (e.symm ▸ no b)
    have le := Finset.card_le_card_of_injOn f (s:=Finset.univ) (t:=N)
      (fun i _ => inside i) (fun _ _ _ _ eq => inj eq)
    simpa using le
  | @res π n A B C old ha hb rule ih =>
    by_cases hc : C∈N
    · let M := N.erase C ∪ {A,B}
      have av : ∀T∈M,T∈π := by
        intro T ht
        rcases Finset.mem_union.mp ht with keep|new
        · exact tl available T keep
        · simp only [Finset.mem_insert,Finset.mem_singleton] at new
          exact new.elim (fun e=>e.symm ▸ ha) (fun e=>e.symm ▸ hb)
      have hM : ∀i,∃T∈M,¬LinClauseSat (w i) T := by
        intro i
        obtain ⟨T,ht,no⟩ := hits i
        by_cases eq : T=C
        · subst T
          rcases snd_res rule (w i) no with p|p
          · exact ⟨A,Finset.mem_union_right _ (by simp),p⟩
          · exact ⟨B,Finset.mem_union_right _ (by simp),p⟩
        · exact ⟨T,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ht⟩),no⟩
      have num := ih M av hM
      have bound : M.card+1≤N.card+({A,B} : Finset (LinClause V)).card := card_step N _ C hc
      have small : ({A,B} : Finset (LinClause V)).card≤2 := Finset.card_le_two
      omega
    · have bound := ih N (tln available hc) hits
      omega
  | @weak π n A B old ha imp ih =>
    by_cases hb : B∈N
    · let M := N.erase B ∪ {A}
      have av : ∀T∈M,T∈π := by
        intro T ht
        rcases Finset.mem_union.mp ht with keep|new
        · exact tl available T keep
        · simp only [Finset.mem_singleton] at new
          exact new.symm ▸ ha
      have hM : ∀i,∃T∈M,¬LinClauseSat (w i) T := by
        intro i
        obtain ⟨T,ht,no⟩ := hits i
        by_cases eq : T=B
        · subst T
          exact ⟨A,Finset.mem_union_right _ (by simp),fun s=>no (imp _ s)⟩
        · exact ⟨T,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,ht⟩),no⟩
      have num := ih M av hM
      have bound : M.card+1 ≤ N.card+({A} : Finset (LinClause V)).card := card_step N _ B hb
      simp only [Finset.card_singleton] at bound
      omega
    · exact ih N (tln available hb) hits
end

abbrev V24 := Fin 24
def axm : Fin 41 → LinClause V24 := ![{({0},true), ({1},true), ({2},true), ({3},true)}, {({4},true), ({5},true), ({6},true), ({7},true)}, {({8},true), ({9},true), ({10},true), ({11},true)}, {({12},true), ({13},true), ({14},true), ({15},true)}, {({16},true), ({17},true), ({18},true), ({19},true)}, {({0},false), ({4},false)}, {({8},false), ({12},false)}, {({8},false), ({16},false)}, {({12},false), ({16},false)}, {({1},false), ({5},false)}, {({9},false), ({13},false)}, {({9},false), ({17},false)}, {({13},false), ({17},false)}, {({2},false), ({6},false)}, {({10},false), ({14},false)}, {({10},false), ({18},false)}, {({14},false), ({18},false)}, {({3},false), ({7},false)}, {({11},false), ({15},false)}, {({11},false), ({19},false)}, {({15},false), ({19},false)}, {({0},false), ({20},true)}, {({1},false), ({21},true)}, {({2},false), ({22},true)}, {({3},false), ({23},true)}, {({4},false), ({20},true)}, {({5},false), ({21},true)}, {({6},false), ({22},true)}, {({7},false), ({23},true)}, {({8},false), ({20},false)}, {({9},false), ({21},false)}, {({10},false), ({22},false)}, {({11},false), ({23},false)}, {({12},false), ({20},false)}, {({13},false), ({21},false)}, {({14},false), ({22},false)}, {({15},false), ({23},false)}, {({16},false), ({20},false)}, {({17},false), ({21},false)}, {({18},false), ({22},false)}, {({19},false), ({23},false)}]
def mask : Fin 41 → Nat := ![1589776, 1589761, 3686433, 3671073, 3179553, 1589777, 6820162, 6390082, 6363202, 2638114, 5775937, 5407297, 5384257, 4727108, 3687457, 3441697, 3426337, 8659336, 3442721, 3688481, 3703841, 2638113, 1589778, 1589780, 1589784, 2638098, 1589793, 1589825, 1589889, 3686689, 3686945, 5776449, 9709697, 3675169, 3679265, 5784129, 9732737, 3245089, 3310625, 5538369, 9978497]
def val (i : Fin 41) (p : V24) := (mask i).testBit p.val
def initial : List (LinClause V24) := List.ofFn axm
def check (i j : Fin 41) := decide (∃q∈axm j,(Odd (q.1.filter (fun v => val i v=true)).card ↔ q.2=true))
theorem privateAssignments : ∀ i j : Fin 41,check i j=decide (i≠j) := by decide +kernel

theorem forty {n π} (pr : Paid initial n π) (empty : (∅ : LinClause V24)∈π) : 40≤n := by
  classical
  have uniq : ∀ A∈initial,∀ i j,¬LinClauseSat (val i) A → ¬LinClauseSat (val j) A → i=j := by
    intro A h i j p q
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp h
    have own (i : Fin 41) (no : ¬LinClauseSat (val i) (axm k)) : i=k := by
      by_contra ne
      have yes : check i k=true := by simp [privateAssignments,ne]
      apply no
      simpa only [check,LinClauseSat,LinEqSat,decide_eq_true_eq] using yes
    exact (own i p).trans (own j q).symm
  have le := tailPrice val uniq pr ({∅} : Finset (LinClause V24))
    (by intro c hc;simp only [Finset.mem_singleton] at hc;exact hc.symm ▸ empty)
    (by intro i;exact ⟨∅,by simp,by simp [LinClauseSat]⟩)
  simp only [Finset.card_singleton] at le
  omega
section
variable {V : Type} [DecidableEq V]
def flip (x : V→Bool) (v : V) (i : V) := if i=v then !(x i) else x i

theorem opposite {x : V→Bool} {f : Finset V} {v : V} (hv : v∈f) (b : Bool) :
    LinEqSat (flip x v) (f,b) ↔ ¬LinEqSat x (f,b) := by
  let S := (f.erase v).filter (fun i=>x i=true)
  have nv : v∉S := by simp [S]
  have h0 : f.filter (fun i=>x i=true) = (if x v then insert v S else S) := by
    ext i
    by_cases he : i=v
    · subst i
      cases hx : x v <;> simp [hx,hv,S]
    · cases hx : x v <;> simp [hx,S,he]
  have h1 : f.filter (fun i=>flip x v i=true) = (if x v then S else insert v S) := by
    ext i
    by_cases he : i=v
    · subst i
      cases hx : x v <;> simp [hx,hv,S,flip]
    · cases hx : x v <;> simp [hx,S,he,flip]
  unfold LinEqSat
  change (Odd (f.filter (fun i=>flip x v i=true)).card ↔ b=true) ↔
    ¬(Odd (f.filter (fun i=>x i=true)).card ↔ b=true)
  rw [h0,h1]
  cases xx : x v <;> cases b <;> simp [xx,Finset.card_insert_of_notMem nv,Nat.odd_iff] <;> omega


end
abbrev Cell := Fin 5 × Fin 4
def red (p : Fin 3) : Fin 5 := ⟨p.val+2,by omega⟩
def mark (h : Fin 4) : LinEq Cell := ({(0,h),(1,h)},false)
def neg (p : Fin 3) (h : Fin 4) : LinClause Cell := {({(red p,h)},false),mark h}

def badPoint (p : Fin 3) (h : Fin 4) (v : Cell) : Bool :=
  decide (v.2=h ∧ (v.1=0 ∨ v.1=red p))

def checks (x : Cell→Bool) (C : LinClause Cell) : Bool :=
  decide (∃q∈C,(Odd (q.1.filter (fun t => x t=true)).card ↔ q.2=true))
theorem checks_correct {x C} : checks x C=true ↔ LinClauseSat x C := by
  unfold checks LinClauseSat LinEqSat
  simp only [decide_eq_true_eq]

theorem coordinates : ∀ (p : Fin 3) (h : Fin 4),
    checks (badPoint p h) (neg p h)=false ∧
    ∀ v : Cell,v.2≠h → checks (flip (badPoint p h) v) (neg p h)=false := by decide +kernel

def WeakFrom (U : LinClause Cell) (h : Fin 4) :=
  ∃p,∀x,LinClauseSat x U → LinClauseSat x (neg p h)
def ResFrom (U : LinClause Cell) (h : Fin 4) :=
  mark h∈U ∧ ∃ (p : Fin 3) (q : LinEq Cell),U.erase q ⊆ neg p h

theorem coordinatesOnly {U : LinClause Cell} {h : Fin 4} (w : WeakFrom U h)
    {q : LinEq Cell} (hq : q∈U) {v : Cell} (hv : v∈q.1) : v.2=h := by
  obtain ⟨p,imp⟩ := w
  by_contra ne
  let x := badPoint p h
  obtain ⟨no,flipno⟩ := coordinates p h
  have bad : ¬LinEqSat x q := by
    intro eq
    have yes := checks_correct.mpr (imp x ⟨q,hq,eq⟩)
    rw [no] at yes
    contradiction
  have flipped : LinEqSat (flip x v) q := (opposite hv q.2).mpr bad
  have yes := checks_correct.mpr (imp (flip x v) ⟨q,hq,flipped⟩)
  rw [flipno v ne] at yes
  contradiction

theorem weakUnique {U : LinClause Cell} (sat : ∃ x,LinClauseSat x U)
    {h k : Fin 4} (w : WeakFrom U h) (z : WeakFrom U k) : h=k := by
  obtain ⟨x,q,hq,yes⟩ := sat
  by_contra diff
  have empty : q.1=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact diff ((coordinatesOnly w hq hv).symm.trans (coordinatesOnly z hq hv))
  obtain ⟨p,imp⟩ := w
  have const : LinEqSat (badPoint p h) q := by
    unfold LinEqSat at yes ⊢
    simpa only [empty,Finset.filter_empty] using yes
  have no := (coordinates p h).1
  have good := checks_correct.mpr (imp (badPoint p h) ⟨q,hq,const⟩)
  rw [no] at good
  contradiction

theorem weakRes {U : LinClause Cell} {h k : Fin 4}
    (w : WeakFrom U h) (r : ResFrom U k) : k=h := by
  exact coordinatesOnly w r.1 (v:=(0,k)) (by simp [mark])

theorem distinctMarks : ∀i j : Fin 4,mark i=mark j → i=j := by decide +kernel
theorem markedNeg : ∀(p : Fin 3) (i j : Fin 4),mark i ∈ neg p j → i=j := by decide +kernel

theorem missing {U : LinClause Cell} (sat : ∃ x,LinClauseSat x U) :
    ¬∀h : Fin 4, WeakFrom U h ∨ ResFrom U h := by
  intro all
  by_cases anyWeak : ∃h,WeakFrom U h
  · obtain ⟨h,w⟩ := anyWeak
    have same (k : Fin 4) : k=h := by
      rcases all k with z|r
      · exact weakUnique sat z w
      · exact weakRes w r
    have bad : (0 : Fin 4)=1 := (same 0).trans (same 1).symm
    exact (by decide : (0 : Fin 4)≠1) bad
  · have source (h : Fin 4) : ResFrom U h := (all h).resolve_left (fun w=>anyWeak ⟨h,w⟩)
    obtain ⟨p,q,sub⟩ := (source 0).2
    have erase (j : Fin 4) (nz : j≠0) : mark j=q := by
      by_contra ne
      exact nz (markedNeg p j 0 (sub (Finset.mem_erase.mpr ⟨ne,(source j).1⟩)))
    have bad := distinctMarks 1 2 ((erase 1 (by decide)).trans (erase 2 (by decide)).symm)
    exact (by decide : (1 : Fin 4)≠2) bad

def raw : Fin 45 → LinClause Cell := ![{({(0,0)},true), ({(0,1)},true), ({(0,2)},true), ({(0,3)},true)}, {({(1,0)},true), ({(1,1)},true), ({(1,2)},true), ({(1,3)},true)}, {({(2,0)},true), ({(2,1)},true), ({(2,2)},true), ({(2,3)},true)}, {({(3,0)},true), ({(3,1)},true), ({(3,2)},true), ({(3,3)},true)}, {({(4,0)},true), ({(4,1)},true), ({(4,2)},true), ({(4,3)},true)}, {({(0,0)},false), ({(1,0)},false)}, {({(0,0)},false), ({(2,0)},false)}, {({(0,0)},false), ({(3,0)},false)}, {({(0,0)},false), ({(4,0)},false)}, {({(1,0)},false), ({(2,0)},false)}, {({(1,0)},false), ({(3,0)},false)}, {({(1,0)},false), ({(4,0)},false)}, {({(2,0)},false), ({(3,0)},false)}, {({(2,0)},false), ({(4,0)},false)}, {({(3,0)},false), ({(4,0)},false)}, {({(0,1)},false), ({(1,1)},false)}, {({(0,1)},false), ({(2,1)},false)}, {({(0,1)},false), ({(3,1)},false)}, {({(0,1)},false), ({(4,1)},false)}, {({(1,1)},false), ({(2,1)},false)}, {({(1,1)},false), ({(3,1)},false)}, {({(1,1)},false), ({(4,1)},false)}, {({(2,1)},false), ({(3,1)},false)}, {({(2,1)},false), ({(4,1)},false)}, {({(3,1)},false), ({(4,1)},false)}, {({(0,2)},false), ({(1,2)},false)}, {({(0,2)},false), ({(2,2)},false)}, {({(0,2)},false), ({(3,2)},false)}, {({(0,2)},false), ({(4,2)},false)}, {({(1,2)},false), ({(2,2)},false)}, {({(1,2)},false), ({(3,2)},false)}, {({(1,2)},false), ({(4,2)},false)}, {({(2,2)},false), ({(3,2)},false)}, {({(2,2)},false), ({(4,2)},false)}, {({(3,2)},false), ({(4,2)},false)}, {({(0,3)},false), ({(1,3)},false)}, {({(0,3)},false), ({(2,3)},false)}, {({(0,3)},false), ({(3,3)},false)}, {({(0,3)},false), ({(4,3)},false)}, {({(1,3)},false), ({(2,3)},false)}, {({(1,3)},false), ({(3,3)},false)}, {({(1,3)},false), ({(4,3)},false)}, {({(2,3)},false), ({(3,3)},false)}, {({(2,3)},false), ({(4,3)},false)}, {({(3,3)},false), ({(4,3)},false)}]
def pos (a : Fin 2) (h : Fin 4) : LinClause Cell :=
  {({(⟨a.val,by omega⟩,h)},false),((mark h).1,true)}
def masks : Fin 24 → Nat := ![540961, 540946, 541202, 541217, 533524, 533569, 272408, 272513, 529441, 529426, 533522, 533537, 541204, 541249, 295448, 295553, 99361, 99346, 164882, 164897, 295444, 295489, 541208, 541313]
def sample (p : Fin 3) (h : Fin 4) (a : Fin 2) (v : Cell) :=
  (masks ⟨8*p.val+2*h.val+a.val,by omega⟩).testBit (4*v.1.val+v.2.val)

theorem rawMark : ∀j h,mark h ∉ raw j := by decide +kernel
theorem posMark : ∀a k h,mark h ∉ pos a k := by decide +kernel
theorem notNeg (p : Fin 3) (h : Fin 4) : mark h∈neg p h := by simp [neg]
theorem blockedRaw : ∀p h i, checks (sample p h 0) (raw i)=true ∨
    checks (sample p h 1) (raw i)=true := by decide +kernel
theorem blockedPos : ∀p h a k, checks (sample p h 0) (pos a k)=true := by decide +kernel
theorem blockedNeg : ∀p h a k,k≠h → checks (sample p h 0) (neg a k)=true := by decide +kernel
theorem badNeg : ∀p h a,checks (sample p h a) (neg p h)=false := by decide +kernel

def Admissible (U A : LinClause Cell) :=
  (∃i,A=raw i) ∨ (∃a k,A=pos a k) ∨ (∃a k,A=neg a k) ∨ A=U

theorem markOrigin {U A : LinClause Cell} {π : List (LinClause Cell)} {h : Fin 4}
    (keep : Admissible U A) (am : A∈π) (mem : mark h∈A)
    (first : ¬∃p,neg p h∈π) : A=U := by
  rcases keep with ⟨i,rfl⟩|⟨a,k,rfl⟩|⟨a,k,rfl⟩|eq
  · exact False.elim (rawMark i h mem)
  · exact False.elim (posMark a k h mem)
  · obtain rfl := markedNeg a h k mem
    exact False.elim (first ⟨a,am⟩)
  · exact eq

theorem weakOrigin {U A : LinClause Cell} {π : List (LinClause Cell)} {h : Fin 4}
    {p : Fin 3} (keep : Admissible U A) (am : A∈π) (first : ¬∃r,neg r h∈π)
    (w : ∀x,LinClauseSat x A → LinClauseSat x (neg p h)) : A=U := by
  have fails (b : Fin 2) (yes : checks (sample p h b) A=true) : False := by
    have falseEq := checks_correct.mpr (w _ (checks_correct.mp yes))
    rw [badNeg] at falseEq
    contradiction
  rcases keep with ⟨i,rfl⟩|⟨a,k,rfl⟩|⟨a,k,rfl⟩|eq
  · rcases blockedRaw p h i with l|r
    · exact False.elim (fails 0 l)
    · exact False.elim (fails 1 r)
  · exact False.elim (fails 0 (blockedPos p h a k))
  · by_cases e : k=h
    · subst k
      exact False.elim (first ⟨a,am⟩)
    · exact False.elim (fails 0 (blockedNeg p h a k e))
  · exact eq

theorem oneSource {π : List (LinClause Cell)} {U : LinClause Cell}
    (guarded : IsLinDerivation (Set.range raw) π) (h : Fin 4)
    (only : ∀A∈π,Admissible U A) (appears : ∃p,neg p h∈π) :
    WeakFrom U h ∨ ResFrom U h := by
  induction guarded with
  | nil =>
    obtain ⟨p,hp⟩ := appears
    simp at hp
  | @ax π A d ax ih =>
    by_cases old : ∃p,neg p h∈π
    · exact ih (fun T ht=>only _ (List.mem_cons_of_mem _ ht)) old
    · obtain ⟨p,hp⟩ := appears
      have eq := (List.mem_cons.mp hp).resolve_right (fun m=>old ⟨p,m⟩)
      obtain ⟨j,rfl⟩ := ax
      exact False.elim (rawMark j h (eq ▸ notNeg p h))
  | @res π A B R d ha hb rule ih =>
    by_cases old : ∃p,neg p h∈π
    · exact ih (fun T ht=>only _ (List.mem_cons_of_mem _ ht)) old
    · obtain ⟨p,hp⟩ := appears
      have eq := (List.mem_cons.mp hp).resolve_right (fun m=>old ⟨p,m⟩)
      obtain ⟨f,fa,fb,re⟩ := rule
      have result := eq.trans re
      have contained : mark h∈A.erase (f,false) ∪ B.erase (f,true) := result ▸ notNeg p h
      right
      rcases Finset.mem_union.mp contained with l|r
      · have left := Finset.mem_of_mem_erase l
        have au := markOrigin (only _ (List.mem_cons_of_mem _ ha)) ha left old
        rw [←au]
        exact ⟨left,p,(f,false),fun _ t=>result.symm ▸ Finset.mem_union_left _ t⟩
      · have rightMem := Finset.mem_of_mem_erase r
        have bu := markOrigin (only _ (List.mem_cons_of_mem _ hb)) hb rightMem old
        rw [←bu]
        exact ⟨rightMem,p,(f,true),fun _ t=>result.symm ▸ Finset.mem_union_right _ t⟩
  | @weak π A R d am imp ih =>
    by_cases old : ∃p,neg p h∈π
    · exact ih (fun T ht=>only _ (List.mem_cons_of_mem _ ht)) old
    · obtain ⟨p,hp⟩ := appears
      have eq := (List.mem_cons.mp hp).resolve_right (fun m=>old ⟨p,m⟩)
      have w : ∀x,LinClauseSat x A → LinClauseSat x (neg p h) := eq.symm ▸ imp
      have au := weakOrigin (only _ (List.mem_cons_of_mem _ am)) am old w
      exact Or.inl ⟨p,au ▸ w⟩

theorem fourNeedMore {π : List (LinClause Cell)} {U : LinClause Cell}
    (guarded : IsLinDerivation (Set.range raw) π)
    (sat : ∃ x,LinClauseSat x U) (only : ∀A∈π,Admissible U A)
    (four : ∀h,∃p,neg p h∈π) : False :=
  missing sat (fun h=>oneSource guarded h only (four h))

def seeds : List (LinClause Cell) := List.ofFn raw
def rawMasks : Fin 45 → Nat := ![541200, 541185, 540705, 525345, 33825, 541201, 540961, 529441, 99361, 540946, 529426, 99346, 528706, 98626, 71746, 540962, 541202, 533522, 164882, 541217, 533537, 164897, 533057, 164417, 141377, 532804, 533524, 541204, 295444, 533569, 541249, 295489, 541729, 295969, 280609, 270728, 272408, 295448, 541208, 272513, 295553, 541313, 296993, 542753, 558113]
def rawVal (i : Fin 45) (c : Cell) := (rawMasks i).testBit (4*c.1.val+c.2.val)
theorem rawCheck : ∀i j,checks (rawVal i) (raw j)=decide (i≠j) := by decide +kernel

theorem rawPrivate : ∀ A∈seeds,∀i j,¬LinClauseSat (rawVal i) A → ¬LinClauseSat (rawVal j) A → i=j := by
  intro A ha i j hi hj
  obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ha
  have own (u : Fin 45) (hu : ¬LinClauseSat (rawVal u) (raw k)) : u=k := by
    by_contra ne
    exact hu (checks_correct.mp (by simp [rawCheck,ne]))
  exact (own i hi).trans (own j hj).symm

theorem satisfiable {π n} (pr : Paid seeds n π) (len : π.length≤66) {A} (am : A∈π) :
    ∃ x,LinClauseSat x A := by
  classical
  have bill : 45+n≤π.length := by
    clear len am
    induction pr with
    | start => simp [seeds]
    | res d _ _ _ ih => simp only [List.length_cons];omega
    | weak d _ _ ih => simp only [List.length_cons];omega
  by_contra none
  push_neg at none
  have cost := tailPrice rawVal rawPrivate pr {A}
    (by intro C hc;simp only [Finset.mem_singleton] at hc;exact hc.symm ▸ am)
    (by intro i;exact ⟨A,by simp,none _⟩)
  simp only [Finset.card_singleton] at cost
  omega

theorem seedDerivation (l : List (LinClause Cell)) (valid : ∀A∈l,A∈Set.range raw) :
    IsLinDerivation (Set.range raw) l := by
  induction l with
  | nil => exact .nil
  | cons a t ih =>
    exact .ax (ih (fun A ha=>valid A (List.mem_cons_of_mem _ ha))) (valid a List.mem_cons_self)

theorem original {π n} (pr : Paid seeds n π) : IsLinDerivation (Set.range raw) π := by
  induction pr with
  | start => exact seedDerivation seeds (fun A ha=>List.mem_ofFn.mp ha)
  | res d ha hb r ih => exact .res ih ha hb r
  | weak d ha w ih => exact .weak ih ha w

def bank : Finset (LinClause Cell) :=
  (Finset.univ.image raw ∪ Finset.univ.image (fun z : Fin 2×Fin 4=>pos z.1 z.2)) ∪
    Finset.univ.image (fun z : Fin 3×Fin 4=>neg z.1 z.2)

theorem bankSize : bank.card=65 := by decide +kernel
theorem bankIn {A U : LinClause Cell} (inside : A∈bank) : Admissible U A := by
  rcases Finset.mem_union.mp inside with l|r
  · rcases Finset.mem_union.mp l with l|r
    · obtain ⟨i,_,eq⟩ := Finset.mem_image.mp l
      exact Or.inl ⟨i,eq.symm⟩
    · obtain ⟨z,_,eq⟩ := Finset.mem_image.mp r
      exact Or.inr (Or.inl ⟨z.1,z.2,eq.symm⟩)
  · obtain ⟨z,_,eq⟩ := Finset.mem_image.mp r
    exact Or.inr (Or.inr (Or.inl ⟨z.1,z.2,eq.symm⟩))

theorem prefixPrice {π n} (pr : Paid seeds n π) (allBank : bank⊆π.toFinset) : 67≤π.length := by
  classical
  by_contra! len
  have small : π.length≤66 := by omega
  have count := Finset.card_sdiff_add_card_eq_card allBank
  rw [bankSize] at count
  have bounded : π.toFinset.card ≤ π.length := List.toFinset_card_le _
  have one : (π.toFinset ∖ bank).card≤1 := by omega
  have allNeg (h : Fin 4) : ∃ p,neg p h∈π := by
    refine ⟨0,List.mem_toFinset.mp (allBank (Finset.mem_union_right _ ?_))⟩
    exact Finset.mem_image.mpr ⟨(0,h),Finset.mem_univ _,rfl⟩
  by_cases ex : ∃ U∈π,U∉bank
  · obtain ⟨U,um,un⟩ := ex
    apply fourNeedMore (original pr) (satisfiable pr small um) _ allNeg
    intro A am
    by_cases ab : A∈bank
    · exact bankIn ab
    · exact Or.inr (Or.inr (Or.inr (Finset.card_le_one.mp one A
        (Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr am,ab⟩) U
        (Finset.mem_sdiff.mpr ⟨List.mem_toFinset.mpr um,un⟩))))
  · let U : LinClause Cell := {((∅ : Finset Cell),false)}
    have sat : ∃x,LinClauseSat x U := by
      refine ⟨fun _=>false,((∅ : Finset Cell),false),by simp [U],?_⟩
      simp [LinEqSat]
    apply fourNeedMore (original pr) sat _ allNeg
    intro A am
    exact bankIn (Classical.byContradiction (fun miss=>ex ⟨A,am,miss⟩))

theorem separated107 {π ρ n m} (pre : Paid seeds n π) (allBank : bank⊆π.toFinset)
    (post : Paid initial m ρ) (empty : (∅ : LinClause V24)∈ρ) :
    107≤π.length+m := by
  have h := prefixPrice pre allBank
  have q := forty post empty
  omega
end PEqualNP.Outside.L_pcx_177.Colors

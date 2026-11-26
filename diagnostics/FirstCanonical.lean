import PEqualNP.Defs
-- General packed decision procedure from L_meta_8405 on project main, itself derived
-- from the L_meta_1673 search engine. The input, sample layout and certificates here are new.

-- The search engine is adapted from PEqualNP.Outside.L_meta_1673 by Trey Kind (pull request 6929, Apache License 2.0).
-- This file declares its own data types (records for the search state and inductive predicates).

namespace PEqualNP.Outside.L_meta_8399
-- Computational declarations are placed first using the organization of public L_meta_8401.
section hz1
variable {R : ℕ → ℕ}
def op (d : Bool) (a b : ℕ) : ℕ := bif d then a ||| b else a &&& b
def Al (R : ℕ → ℕ) (d : Bool) (a b : ℕ) : Prop := (R a &&& R b) ≤ (bif d then 1 else 0)
def Z0 : ℕ → ℕ := fun _ => 0
inductive Sol (R : ℕ → ℕ) (m T : ℕ) : ℕ → Set ℕ → Prop
  | done {q : ℕ} {S : Set ℕ} : T ∈ S → Sol R m T q S
  | un {q : ℕ} {S : Set ℕ} {a : ℕ} : a ∈ S → Sol R m T q (insert (a ^^^ m) S) → Sol R m T (q + 1) S
  | bi {q : ℕ} {S : Set ℕ} {d : Bool} {a b : ℕ} : a ∈ S → b ∈ S → Al R d a b →
      Sol R m T q (insert (op d a b) S) → Sol R m T (q + 1) S
inductive Live (R : ℕ → ℕ) (m T : ℕ) : ℕ → ℕ → Finset ℕ → Prop
  | stop : Live R m T 0 0 {T}
  | un {k t : ℕ} {a : ℕ} {U : Finset ℕ} : Live R m T k t (insert (a ^^^ m) U) →
      Live R m T (k + 1) (t + 1) (insert a U)
  | bi {k t : ℕ} {d : Bool} {a b : ℕ} {U : Finset ℕ} : a ≠ b → Al R d a b → Live R m T k t (insert (op d a b) U) →
      Live R m T (k + 1) t (insert a (insert b U))
end hz1
structure WireEvent where
  inputs : Finset ℕ
  output : ℕ

def WireEvent.Fires (a : WireEvent) (S S' : Finset ℕ) : Prop :=
  ∃ U, S = a.inputs ∪ U ∧ S' = insert a.output U

theorem WireEvent.swap {a b : WireEvent} {S M T : Finset ℕ}
    (first : a.Fires S M) (second : b.Fires M T) (independent : a.output ∉ b.inputs) :
    ∃ N, b.Fires S N ∧ a.Fires N T := by
  obtain ⟨U,es,em⟩ := first
  obtain ⟨V,em',et⟩ := second
  have mids : insert a.output U = b.inputs ∪ V := em.symm.trans em'
  have included : b.inputs ⊆ U := by
    intro x h
    have mem : x ∈ insert a.output U := by rw [mids]; exact Finset.mem_union_left _ h
    rcases Finset.mem_insert.mp mem with rfl | hu
    · exact False.elim (independent h)
    · exact hu
  have needed : a.output ∈ V := by
    have mem : a.output ∈ b.inputs ∪ V := by rw [←mids]; exact Finset.mem_insert_self _ _
    exact (Finset.mem_union.mp mem).resolve_left independent
  let C := U ∩ V
  have lu : U = b.inputs ∪ C := by
    ext x
    change x ∈ U ↔ x ∈ b.inputs ∪ (U ∩ V)
    simp only [Finset.mem_union,Finset.mem_inter]
    constructor
    · intro hx
      have v : x ∈ insert a.output U := Finset.mem_insert_of_mem hx
      rw [mids] at v
      rcases Finset.mem_union.mp v with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hx,h⟩
    · exact fun h => h.elim (fun z => included z) And.left
  have lv : V = insert a.output C := by
    ext x
    change x ∈ V ↔ x ∈ insert a.output (U ∩ V)
    simp only [Finset.mem_insert,Finset.mem_inter]
    constructor
    · intro hx
      have v : x ∈ b.inputs ∪ V := Finset.mem_union_right _ hx
      rw [←mids] at v
      rcases Finset.mem_insert.mp v with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h,hx⟩
    · rintro (rfl | h)
      · exact needed
      · exact h.2
  refine ⟨insert b.output (a.inputs ∪ C), ⟨a.inputs ∪ C, ?_, rfl⟩, ⟨insert b.output C, ?_, ?_⟩⟩
  · rw [es,lu]
    ac_rfl
  · ext x
    simp only [Finset.mem_insert, Finset.mem_union]
    tauto
  · rw [et,lv,Finset.insert_comm]

inductive OrderedGate (m : ℕ)
  | inv (x : ℕ)
  | bin (d : Bool) (x y : ℕ)

def OrderedGate.event {m} : OrderedGate m → WireEvent
  | .inv x => ⟨{x}, x ^^^ m⟩
  | .bin d x y => ⟨{x,y}, op d x y⟩

def OrderedGate.legal {m} (R : ℕ → ℕ) : OrderedGate m → Prop
  | .inv _ => True
  | .bin d x y => x ≠ y ∧ Al R d x y

inductive WireSchedule (R : ℕ → ℕ) (m T : ℕ) : List (OrderedGate m) → Finset ℕ → Prop
  | done : WireSchedule R m T [] {T}
  | cons {g xs S M} : g.legal R → g.event.Fires S M → WireSchedule R m T xs M → WireSchedule R m T (g::xs) S

def OrderedGate.inversion {m} : OrderedGate m → ℕ
  | .inv _ => 1
  | .bin _ _ _ => 0

theorem Live.finiteSchedule {R m T k t S} (h : Live R m T k t S) :
    ∃ xs, WireSchedule R m T xs S ∧ xs.length = k ∧ (xs.map OrderedGate.inversion).sum = t := by
  induction h with
  | stop => exact ⟨[], .done, rfl, rfl⟩
  | @un k t a U _ ih =>
    obtain ⟨xs,run,hn,ht⟩ := ih
    refine ⟨.inv a :: xs, .cons (by trivial) ⟨U,by simp [OrderedGate.event],rfl⟩ run, ?_, ?_⟩
    · simp [hn]
    · simp [OrderedGate.inversion,ht,Nat.add_comm]
  | @bi k t d a b U hn ha _ ih =>
    obtain ⟨xs,run,hk,ht⟩ := ih
    refine ⟨.bin d a b :: xs, .cons ⟨hn,ha⟩ ⟨U,by simp [OrderedGate.event],rfl⟩ run, ?_, ?_⟩
    · simp [hk]
    · simp [OrderedGate.inversion,ht]

theorem WireSchedule.toLive {R m T xs S} (h : WireSchedule R m T xs S) :
    Live R m T xs.length (xs.map OrderedGate.inversion).sum S := by
  induction h with
  | done => exact .stop
  | @cons g xs S M ok fires tail ih =>
    obtain ⟨U,rfl,rfl⟩ := fires
    cases g with
    | inv a =>
      simpa [OrderedGate.event, OrderedGate.inversion,Nat.add_comm] using Live.un ih
    | bin d a b =>
      simpa [OrderedGate.event, OrderedGate.inversion] using Live.bi ok.1 ok.2 ih

theorem WireSchedule.swapAt {R m T} {a b : OrderedGate m} (pre post : List (OrderedGate m))
    (independent : a.event.output ∉ b.event.inputs) {S}
    (h : WireSchedule R m T (pre ++ a :: b :: post) S) : WireSchedule R m T (pre ++ b :: a :: post) S := by
  induction pre generalizing S with
  | nil =>
    cases h with
    | cons al af h1 =>
      cases h1 with
      | cons bl bf h2 =>
        obtain ⟨M,bf',af'⟩ := WireEvent.swap af bf independent
        exact .cons bl bf' (.cons al af' h2)
  | cons c cs ih =>
    cases h with
    | cons cl cf rest => exact .cons cl cf (ih rest)

def scheduleScore {α : Type} (key : α → ℕ) : List α → ℕ
  | [] => 0
  | a::xs => (xs.length+1)*key a + scheduleScore key xs

theorem scheduleScore_swap {α : Type} (key : α → ℕ) (pre post : List α) {a b : α}
    (smaller : key b < key a) :
    scheduleScore key (pre ++ b :: a :: post) < scheduleScore key (pre ++ a :: b :: post) := by
  induction pre with
  | nil =>
    simp only [List.nil_append,scheduleScore,List.length_cons,Nat.add_mul,one_mul]
    omega
  | cons x xs ih =>
    simp only [List.cons_append,scheduleScore,List.length_append,List.length_cons]
    exact Nat.add_lt_add_left ih _

theorem WireSchedule.canonical {R m T xs S} (h : WireSchedule R m T xs S) (key : OrderedGate m → ℕ) :
    ∃ ys, WireSchedule R m T ys S ∧ ys.Perm xs ∧
      ∀ pre post a b, ys = pre ++ a :: b :: post → a.event.output ∉ b.event.inputs → key a ≤ key b := by
  classical
  let P (n : ℕ) := ∃ ys, WireSchedule R m T ys S ∧ ys.Perm xs ∧ scheduleScore key ys = n
  have someScore : ∃ n, P n := ⟨_,xs,h,List.Perm.refl _,rfl⟩
  obtain ⟨ys,run,perm,eq⟩ := Nat.find_spec someScore
  refine ⟨ys,run,perm,?_⟩
  rintro pre post a b rfl independent
  by_contra! less
  have alternative := run.swapAt pre post independent
  have swapP : (pre ++ b :: a :: post).Perm (pre ++ a :: b :: post) :=
    (List.Perm.swap a b post).append_left pre
  have lower := scheduleScore_swap key pre post less
  rw [eq] at lower
  exact Nat.find_min someScore lower ⟨_,alternative,swapP.trans perm,rfl⟩

-- Move a chosen event across an arbitrary interval of events whose outputs it does not read.
def headValue {α : Type} (key : α → ℕ) : List α → ℕ
  | [] => 0
  | a :: _ => key a

theorem WireSchedule.firstCanonical {R m T xs S} (h : WireSchedule R m T xs S)
    (key : OrderedGate m → ℕ) (admit : List (OrderedGate m) → Prop)
    (initial : admit xs) (stable : ∀ {a b : List (OrderedGate m)}, a.Perm b → admit b → admit a) :
    ∃ ys, WireSchedule R m T ys S ∧ admit ys ∧
      (∀ zs, WireSchedule R m T zs S → admit zs → headValue key ys ≤ headValue key zs) ∧
      ∀ pre post a b, ys = pre ++ a :: b :: post →
        a.event.output ∉ b.event.inputs → key a ≤ key b := by
  classical
  let H (n : ℕ) := ∃ us, WireSchedule R m T us S ∧ admit us ∧ headValue key us = n
  have someH : ∃ n, H n := ⟨_, xs, h, initial, rfl⟩
  let lo := Nat.find someH
  obtain ⟨base,run,ok,low⟩ := Nat.find_spec someH
  let W (n : ℕ) := ∃ us, WireSchedule R m T us S ∧ admit us ∧
    headValue key us = lo ∧ scheduleScore key us = n
  have someW : ∃ n, W n := ⟨_,base,run,ok,low,rfl⟩
  obtain ⟨ys,program,valid,head,score⟩ := Nat.find_spec someW
  have minimal (zs) (hz : WireSchedule R m T zs S) (okz : admit zs) :
      headValue key ys ≤ headValue key zs := by
    rw [head]
    exact Nat.find_min' someH ⟨zs,hz,okz,rfl⟩
  refine ⟨ys,program,valid,minimal,?_⟩
  rintro pre post a b rfl independent
  by_contra! smaller
  have other := program.swapAt pre post independent
  have perm : (pre ++ b :: a :: post).Perm (pre ++ a :: b :: post) :=
    (List.Perm.swap a b post).append_left pre
  have ok' := stable perm valid
  cases pre with
  | nil =>
    have contradiction := minimal _ other ok'
    change key a ≤ key b at contradiction
    omega
  | cons c cs =>
    have same : headValue key ((c::cs) ++ b :: a :: post) = lo := by
      change key c = lo
      exact head
    have better := scheduleScore_swap key (c::cs) post smaller
    rw [score] at better
    exact Nat.find_min someW better ⟨_,other,ok',same,rfl⟩

end PEqualNP.Outside.L_meta_8399

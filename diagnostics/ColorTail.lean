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
      exact no (of_decide_eq_true (show decide (∃q∈axm k,(Odd (q.1.filter (fun v => val i v=true)).card ↔ q.2=true))=true from yes))
    exact (own i p).trans (own j q).symm
  have le := tailPrice val uniq pr ({∅} : Finset (LinClause V24))
    (by intro c hc;simp only [Finset.mem_singleton] at hc;exact hc.symm ▸ empty)
    (by intro i;exact ⟨∅,by simp,by simp [LinClauseSat]⟩)
  simp only [Finset.card_singleton] at le
  omega
end PEqualNP.Outside.L_pcx_177.Colors

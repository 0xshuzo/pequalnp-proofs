import PEqualNP.Defs

namespace Load2585
variable {X Y : Type*} [DecidableEq X] [DecidableEq Y]

inductive Pool (X : Type*) [DecidableEq X] : Nat → Finset (Finset X) → Prop where
  | raw {S} (h : ∀ A∈S, A.card≤1) : Pool X 0 S
  | join {k S} (pr : Pool X k S) {A B : Finset X} (ha : A∈S) (hb : B∈S) :
      Pool X (k+1) (insert (A∪B) S)

end Load2585

namespace Shared3457
open Load2585
variable {X P : Type*} [Fintype X] [Fintype P] [DecidableEq X] [DecidableEq P]

abbrev Sig (X P : Type*) := Finset X × Finset P

def meet (a b : Sig X P) : Sig X P := (a.1∩b.1,a.2∪b.2)
def join (a b : Sig X P) : Sig X P := (a.1∪b.1,a.2∩b.2)

def Sound (N : P→Finset X) (a : Sig X P) := ∀p∈a.2,a.1⊆N p

inductive Program (N : P→Finset X) : Nat→Finset (Sig X P)→Prop where
  | base {O} (correct : ∀a∈O,Sound N a) (small : ∀a∈O,a.1.card≤1 ∨ a.2=∅) : Program N 0 O
  | meetStep {k O} (pr : Program N k O) {a b} (ha : a∈O) (hb : b∈O) : Program N k (insert (meet a b) O)
  | joinStep {k O} (pr : Program N k O) {a b} (ha : a∈O) (hb : b∈O) : Program N (k+1) (insert (join a b) O)

theorem sound {N : P→Finset X} {k O} (prog : Program N k O) : ∀a∈O,Sound N a := by
  induction prog with
  | base correct _ => exact correct
  | @meetStep k O pr a b ha hb ih =>
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl|old
    · intro p pp x xx
      rcases Finset.mem_union.mp pp with l|r
      · exact ih a ha p l (Finset.mem_inter.mp xx).1
      · exact ih b hb p r (Finset.mem_inter.mp xx).2
    · exact ih s old
  | @joinStep k O pr a b ha hb ih =>
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl|old
    · intro p pp x xx
      rcases Finset.mem_union.mp xx with l|r
      · exact ih a ha p (Finset.mem_inter.mp pp).1 l
      · exact ih b hb p (Finset.mem_inter.mp pp).2 r
    · exact ih s old

def fits (N : P→Finset X) (a : Sig X P) (T : Finset X) := ∀p∈a.2,a.1⊆T ∧ T⊆N p

theorem simulate (N : P→Finset X) (linear : ∀p q,p≠q→(N p∩N q).card≤1)
    {k O} (prog : Program N k O) :
    ∃S : Finset (Finset X),Pool X k S ∧ (∀T : Finset X,T.card≤1→T∈S) ∧
      ∀a∈O,∃T∈S,fits N a T := by
  classical
  induction prog with
  | @base O correct small =>
    let S := Finset.univ.filter fun T : Finset X=>T.card≤1
    have all (T : Finset X) (sz : T.card≤1) : T∈S := by simp [S,sz]
    refine ⟨S,.raw (fun _ mem=>(Finset.mem_filter.mp mem).2),all,?_⟩
    intro a ha
    rcases small a ha with sz|none
    · exact ⟨a.1,all _ sz,fun p hp=>⟨Finset.Subset.refl _,correct a ha p hp⟩⟩
    · exact ⟨∅,all _ (by simp),fun p hp=>by simp [none] at hp⟩
  | @joinStep k O pr a b ha hb ih =>
    obtain ⟨S,pool,small,h⟩ := ih
    obtain ⟨A,as,fa⟩ := h a ha
    obtain ⟨B,bs,fb⟩ := h b hb
    refine ⟨insert (A∪B) S,.join pool as bs,fun T sz=>Finset.mem_insert_of_mem (small _ sz),?_⟩
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl|old
    · refine ⟨A∪B,Finset.mem_insert_self _ _,?_⟩
      intro p hp
      obtain ⟨l,r⟩ := Finset.mem_inter.mp hp
      exact ⟨Finset.union_subset_union (fa p l).1 (fb p r).1,Finset.union_subset (fa p l).2 (fb p r).2⟩
    · obtain ⟨T,mem,fit⟩ := h s old
      exact ⟨T,Finset.mem_insert_of_mem mem,fit⟩
  | @meetStep k O pr a b ha hb ih =>
    obtain ⟨S,pool,small,h⟩ := ih
    refine ⟨S,pool,small,?_⟩
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl|old
    · let m := meet a b
      have correct : Sound N m := sound (Program.meetStep pr ha hb) _ (Finset.mem_insert_self _ _)
      by_cases short : m.1.card≤1
      · exact ⟨m.1,small _ short,fun p hp=>⟨Finset.Subset.refl _,correct p hp⟩⟩
      · by_cases live : m.2.Nonempty
        · obtain ⟨p,hp⟩ := live
          have unique (q : P) (hq : q∈m.2) : q=p := by
            by_contra distinct
            have sub : m.1⊆N q∩N p := Finset.subset_inter (correct q hq) (correct p hp)
            exact short ((Finset.card_le_card sub).trans (linear q p distinct))
          rcases Finset.mem_union.mp hp with left|right
          · obtain ⟨T,mem,fit⟩ := h a ha
            refine ⟨T,mem,?_⟩
            intro q hq
            rw [unique q hq]
            exact ⟨Finset.Subset.trans Finset.inter_subset_left (fit p left).1,(fit p left).2⟩
          · obtain ⟨T,mem,fit⟩ := h b hb
            refine ⟨T,mem,?_⟩
            intro q hq
            rw [unique q hq]
            exact ⟨Finset.Subset.trans Finset.inter_subset_right (fit p right).1,(fit p right).2⟩
        · exact ⟨∅,small _ (by simp),fun p hp=>False.elim (live ⟨p,hp⟩)⟩
    · exact h s old

-- Each semantic label can be computed without unfolding its generating circuit.
def signature (N : P→Finset X) (f : Finset X→Bool) : Sig X P :=
  (Finset.univ.filter (fun x=>f {x}=true),Finset.univ.filter (fun p=>f (N p)ᶜ=false))

theorem meetEval (N : P→Finset X) (f g : Finset X→Bool) :
    signature N (fun s=>f s && g s)=meet (signature N f) (signature N g) := by
  apply Prod.ext <;> ext t <;> simp [signature,meet]

theorem joinEval (N : P→Finset X) (f g : Finset X→Bool) :
    signature N (fun s=>f s || g s)=join (signature N f) (signature N g) := by
  apply Prod.ext <;> ext t <;> simp [signature,join]

end Shared3457

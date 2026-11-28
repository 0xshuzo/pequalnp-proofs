import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_33669
variable {E : Type} [DecidableEq E]
abbrev Tree (E : Type) := List (List Bool × E)
def node (t : Tree E) (a : List Bool) := (t.find? (fun r => decide (r.1=a))).map Prod.snd
def step (t : Tree E) (S : Finset E) (a : List Bool) :=
  (node t a).elim a (fun e => a++[decide (e∈S)])
def walk (t : Tree E) (S : Finset E) : Nat → List Bool
  | 0 => []
  | d+1 => step t S (walk t S d)
def forced (t : Tree E) (a : List Bool) :=
  ((t.filter (fun r => (r.1++[true]).isPrefixOf a)).map Prod.snd).toFinset

theorem walk_fold (t : Tree E) (S : Finset E) (n : Nat) :
    (List.range n).foldl (fun a _ => step t S a) []=walk t S n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.range_succ, List.foldl_append,ih,walk]

theorem pref_append (q a : List Bool) (b : Bool) :
    (q++[true]).isPrefixOf (a++[b])=true ↔
      (q++[true]).isPrefixOf a=true ∨ q=a ∧ b=true := by
  induction q generalizing a with
  | nil => cases a with
    | nil => cases b <;> decide
    | cons c cs => cases c <;> simp [List.isPrefixOf]
  | cons c cs ih =>
    cases a with
    | nil => cases c <;> cases b <;> cases cs <;> simp [List.isPrefixOf]
    | cons d ds =>
      cases c <;> cases d <;> simp [List.isPrefixOf,ih]

theorem forced_mem (t : Tree E) (a : List Bool) (e : E) :
    e∈forced t a ↔ ∃ q, (q,e)∈t ∧ (q++[true]).isPrefixOf a=true := by
  constructor
  · intro h
    obtain ⟨⟨q,e'⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    exact ⟨q,(List.mem_filter.mp hm).1,(List.mem_filter.mp hm).2⟩
  · rintro ⟨q,hm,hit⟩
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(q,e),List.mem_filter.mpr ⟨hm,hit⟩,rfl⟩)

theorem member_node {t : Tree E} (uniq : (t.map Prod.fst).Nodup)
    {a : List Bool} {e : E} (h : (a,e)∈t) : node t a=some e := by
  induction t with
  | nil => simp at h
  | cons r rs ih =>
    obtain ⟨r,v⟩ := r
    have nd := List.nodup_cons.mp uniq
    rcases List.mem_cons.mp h with eq|hm
    · obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
      simp [node,List.find?]
    · have ne : r≠a := by
        rintro rfl
        exact nd.1 (List.mem_map.mpr ⟨(r,e),hm,rfl⟩)
      simpa [node,List.find?,ne] using ih nd.2 hm

theorem node_member {t : Tree E} {a : List Bool} {e : E} (h : node t a=some e) : (a,e)∈t := by
  unfold node at h
  cases eq : t.find? (fun r => decide (r.1=a)) with
  | none => simp [eq] at h
  | some r =>
    have k : r.1=a := of_decide_eq_true (List.find?_some eq)
    have s : r.2=e := by simpa [eq] using h
    have mem := List.mem_of_find?_eq_some eq
    simpa [←k,←s] using mem

theorem extends (t : Tree E) (S : Finset E) (a : List Bool) :
    forced t a⊆forced t (step t S a) := by
  intro e hm
  obtain ⟨q,hq,pre⟩ := (forced_mem _ _ _).mp hm
  apply (forced_mem _ _ _).mpr
  refine ⟨q,hq,?_⟩
  cases eq : node t a with
  | none => simpa [step,eq] using pre
  | some v => simpa [step,eq] using (pref_append q a (decide (v∈S))).mpr (Or.inl pre)

theorem forced_sub (t : Tree E) (uniq : (t.map Prod.fst).Nodup) (S : Finset E) (n : Nat) :
    forced t (walk t S n)⊆S := by
  induction n with
  | zero =>
    intro e he
    obtain ⟨q,_,pre⟩ := (forced_mem _ _ _).mp he
    cases q <;> simp [walk,List.isPrefixOf] at pre
  | succ n ih =>
    let a := walk t S n
    intro e he
    change e∈forced t (step t S a) at he
    cases eq : node t a with
    | none => exact ih (by simpa [step,eq,a] using he)
    | some v =>
      obtain ⟨q,hq,pre⟩ := (forced_mem _ _ _).mp he
      have h := (pref_append q a (decide (v∈S))).mp (by simpa [step,eq] using pre)
      rcases h with old|⟨rfl,yes⟩
      · exact ih ((forced_mem _ _ _).mpr ⟨q,hq,old⟩)
      · have match' := member_node uniq hq
        have same := Option.some.inj (match'.symm.trans eq)
        exact same ▸ of_decide_eq_true yes

theorem sandwich (t : Tree E) (S U : Finset E) (n : Nat)
    (inside : U⊆S) (covers : forced t (walk t S n)⊆U) : walk t U n=walk t S n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    let a := walk t S n
    have old : forced t a ⊆ U := (extends t S a).trans covers
    have same := ih old
    change step t U (walk t U n)=step t S a
    rw [same]
    change step t U a=step t S a
    unfold step
    cases hn : node t a with
    | none => rfl
    | some e =>
      have cmp : e∈U ↔ e∈S := ⟨fun h => inside h,fun h => covers (by
        change e∈forced t (step t S a)
        apply (forced_mem _ _ _).mpr
        refine ⟨a,node_member hn,?_⟩
        simp [step,hn,h])⟩
      simp [cmp]

end PEqualNP.Outside.L_meta_33669

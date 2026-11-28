import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17661

open PEqualNP.CircuitLowerBounds
abbrev Bank := Nat → Bool
def gateValue (g : Gate) (x : Bank) : Bool := g.op.eval (g.inputs.map x)

def step (n : Nat) (g : Gate) (x : Bank) : Bank :=
  fun j => if j = n then gateValue g x else x j

def execute : (n : Nat) → List Gate → Bank → Bank
  | _, [], x => x
  | n, g :: gs, x => execute (n+1) gs (step n g x)

def pullList (l : List Bool) : Bank := fun i => l.getD i false

def listGate (l : List Bool) (g : Gate) : List Bool :=
  l ++ [gateValue g (pullList l)]

theorem pullStep (l : List Bool) (g : Gate) :
    pullList (listGate l g) = step l.length g (pullList l) := by
  funext i
  by_cases eq : i = l.length
  · subst i
    simp [pullList, listGate, step, List.getD_eq_getElem?_getD]
  · by_cases lt : i < l.length
    · simpa only [pullList, listGate, step, if_neg eq] using
        List.getD_append l [gateValue g (pullList l)] false i lt
    · have hlo : l.length ≤ i := by omega
      have hhi : (listGate l g).length ≤ i := by simp [listGate]; omega
      simp only [pullList, step, if_neg eq, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none hlo, List.getElem?_eq_none hhi, Option.getD_none]

theorem pullExecute (gs : List Gate) (l : List Bool) :
    pullList (gs.foldl listGate l) = execute l.length gs (pullList l) := by
  induction gs generalizing l with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih, execute, pullStep]
    simp [listGate]

def charge (g : Gate) : Nat := match g.op with | .or => 1 | _ => 0

def ZeroCert (f : Bank → Bool) (x : Bank) (u : Nat) : Prop :=
  ∃ S : Finset Nat, S.card ≤ u ∧ (∀ i ∈ S, x i = false) ∧
    ∀ y : Bank, (∀ i ∈ S, y i = false) → f y = false

theorem gateZero (g : Gate) (x : Bank)
    (ao : g.op = GateOp.and ∨ g.op = GateOp.or) (deg : g.inputs.length ≤ 2)
    (fail : gateValue g x = false) : ZeroCert (gateValue g) x (1 + charge g) := by
  rcases ao with h | h
  · have andTest (y : Bank) : gateValue g y = false ↔ ∃ i ∈ g.inputs, y i = false := by
      simp [gateValue, h, GateOp.eval, List.all_eq_false]
    obtain ⟨i, hi, zero⟩ := (andTest x).1 fail
    exact ⟨{i}, by simp [charge,h], by simpa using zero, fun y hy =>
      (andTest y).2 ⟨i,hi,hy i (Finset.mem_singleton_self _)⟩⟩
  · have orTest (y : Bank) : gateValue g y = false ↔ ∀ i ∈ g.inputs, y i = false := by
      simp [gateValue, h, GateOp.eval, List.any_eq_false]
    exact ⟨g.inputs.toFinset, by simpa [charge,h] using le_trans (List.toFinset_card_le _) deg,
      fun i hi => (orTest x).1 fail i (List.mem_toFinset.mp hi),
      fun y hy => (orTest y).2 (fun i hi => hy i (List.mem_toFinset.mpr hi))⟩

theorem gatePull (n : Nat) (g : Gate) (f : Bank → Bool) (x : Bank) (u : Nat)
    (ao : g.op = GateOp.and ∨ g.op = GateOp.or) (deg : g.inputs.length ≤ 2)
    (c : ZeroCert f (step n g x) u) : ZeroCert (fun y => f (step n g y)) x (u + charge g) := by
  classical
  obtain ⟨S,sz,z,keep⟩ := c
  by_cases hn : n ∈ S
  · have out0 : gateValue g x = false := by simpa [step] using z n hn
    obtain ⟨T,ts,tz,tk⟩ := gateZero g x ao deg out0
    have erase := Finset.card_erase_add_one hn
    have union := Finset.card_union_le (S.erase n) T
    refine ⟨(S.erase n) ∪ T, by omega, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_union.mp hi with hi | hi
      · obtain ⟨ne,hs⟩ := Finset.mem_erase.mp hi
        simpa [step,ne] using z i hs
      · exact tz i hi
    · intro y hy
      apply keep
      intro i hi
      by_cases ne : i=n
      · subst i
        simpa [step] using tk y (fun j hj => hy j (Finset.mem_union_right _ hj))
      · simpa [step,ne] using hy i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨ne,hi⟩))
  · refine ⟨S,by omega,?_,?_⟩
    · intro i hi
      have ne : i≠n := fun eq => hn (eq ▸ hi)
      simpa [step,ne] using z i hi
    · intro y hy
      apply keep
      intro i hi
      have ne : i≠n := fun eq => hn (eq ▸ hi)
      simpa [step,ne] using hy i hi

theorem fullZero (gs : List Gate) (n o : Nat) (x : Bank)
    (ao : ∀ g∈gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2)
    (fails : execute n gs x o = false) :
    ZeroCert (fun y => execute n gs y o) x (1 + (gs.map charge).sum) := by
  induction gs generalizing n x with
  | nil =>
    refine ⟨{o}, by simp, ?_, ?_⟩
    · simpa [execute] using fails
    · intro y hy
      exact hy o (Finset.mem_singleton_self _)
  | cons g gs ih =>
    have hg := ao g List.mem_cons_self
    have cert := ih (n+1) (step n g x) (fun t ht => ao t (List.mem_cons_of_mem _ ht)) fails
    have h := gatePull n g (fun y => execute (n+1) gs y o) x _ hg.1 hg.2 cert
    simpa only [execute, List.map_cons, List.sum_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def zeroCharge : (n : Nat) → List Gate → Bank → Nat
  | _, [], _ => 0
  | n, g :: gs, x =>
    (if gateValue g x then 0 else charge g) + zeroCharge (n+1) gs (step n g x)

theorem gatePullOnRow (n : Nat) (g : Gate) (f : Bank → Bool) (x : Bank) (u : Nat)
    (ao : g.op = GateOp.and ∨ g.op = GateOp.or) (deg : g.inputs.length ≤ 2)
    (c : ZeroCert f (step n g x) u) :
    ZeroCert (fun y => f (step n g y)) x (u + (if gateValue g x then 0 else charge g)) := by
  classical
  cases h : gateValue g x with
  | false => simpa [h] using gatePull n g f x u ao deg c
  | true =>
    change ZeroCert (fun y => f (step n g y)) x u
    obtain ⟨S,sz,z,keep⟩ := c
    have absent : n ∉ S := by
      intro hn
      have hf := z n hn
      simp [step,h] at hf
    refine ⟨S, sz, ?_, ?_⟩
    · intro i hi
      have ne : i≠n := fun eq => absent (eq ▸ hi)
      simpa [step,ne] using z i hi
    · intro y hy
      apply keep
      intro i hi
      have ne : i≠n := fun eq => absent (eq ▸ hi)
      simpa [step,ne] using hy i hi

theorem fullZeroOnRow (gs : List Gate) (n o : Nat) (x : Bank)
    (ao : ∀ g∈gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2)
    (fails : execute n gs x o = false) :
    ZeroCert (fun y => execute n gs y o) x (1 + zeroCharge n gs x) := by
  induction gs generalizing n x with
  | nil =>
    refine ⟨{o}, by simp [zeroCharge], ?_, ?_⟩
    · simpa [execute] using fails
    · intro y hy
      exact hy o (Finset.mem_singleton_self _)
  | cons g gs ih =>
    have hg := ao g List.mem_cons_self
    have cert := ih (n+1) (step n g x) (fun t ht => ao t (List.mem_cons_of_mem _ ht)) fails
    have h := gatePullOnRow n g (fun y => execute (n+1) gs y o) x _ hg.1 hg.2 cert
    simpa only [execute, zeroCharge, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def raisePin (x : Bank) (v : Nat) : Bank := fun i => if i = v then true else x i

theorem activeSwitches (gs : List Gate) (n o : Nat) (x : Bank) (S : Finset Nat)
    (ao : ∀ g∈gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2)
    (baseFalse : execute n gs x o=false)
    (rise : ∀ v ∈ S, execute n gs (raisePin x v) o=true) :
    S.card ≤ 1 + zeroCharge n gs x := by
  classical
  obtain ⟨T,ts,z,keep⟩ := fullZeroOnRow gs n o x ao baseFalse
  apply le_trans (Finset.card_le_card (s:=S) (t:=T) ?_) ts
  intro v hv
  by_contra hn
  have f := keep (raisePin x v) (by
    intro i hi
    have ne : i ≠ v := fun eq => hn (eq ▸ hi)
    simpa [raisePin,ne] using z i hi)
  change execute n gs (raisePin x v) o = false at f
  rw [rise v hv] at f
  contradiction


open PEqualNP.HeptadCover PEqualNP.GenericRejection PEqualNP.MetaComplexity
abbrev I := Fin 13
abbrev PS := Finset I
abbrev lines := singerLines3
def Q : PS := {0,1,2,5}
def base := incidenceInput Q (missLines lines Q)
def crit : Finset Nat := {3,4,6,7,8,9,10,11,12,13,14,15,17,18,19,22,23,24,25}
def kPin : Fin 19 → Nat := ![3,4,6,7,8,9,10,11,12,13,14,15,17,18,19,22,23,24,25]
def kPoint : Fin 19 → I := ![3,4,6,7,8,9,10,11,12,0,1,2,0,1,2,5,0,1,0]
def kLine : Fin 19 → I := ![3,3,3,7,7,8,7,8,3,0,1,2,4,5,6,9,10,11,12]
def row (i : Fin 19) := incidenceInput {kPoint i} {kLine i}
theorem actual : ∀ i : Fin 19, kPoint i ∈ lines (kLine i) := by decide
theorem allPins : crit = Finset.univ.image kPin := by decide
theorem rowCover : ∀ (i : Fin 19) (j : Fin 26), pullList base j.val = false →
    j.val ≠ kPin i → pullList (row i) j.val = false := by decide
theorem qArc : Q ∈ quadrangles lines := by
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,by decide⟩,by decide⟩

theorem runEq (C : Circuit) (l : List Bool) (hl : l.length=26) :
    C.eval l = execute 26 C.gates (pullList l) C.output := by
  have h := congrFun (pullExecute C.gates l) C.output
  rw [hl] at h
  exact h

theorem charged (C : Circuit) (mc : Monotone2 C) (ok : RightOnIncidentPairs lines C)
    (fail : C.eval base = false) : 18 ≤ (C.gates.map charge).sum := by
  classical
  have bl : base.length=26 := by simp [base,incidenceInput]
  rw [runEq C base bl] at fail
  obtain ⟨S,sz,z,keep⟩ := fullZero C.gates 26 C.output (pullList base)
    (fun g hg => ⟨by
      rcases (mc g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (mc g hg).2⟩) fail
  have sub : crit ⊆ S := by
    rw [allPins]
    intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    by_contra hi
    have bad := keep (pullList (row i)) (by
      intro j hj
      have ne : j≠kPin i := fun eq => hi (eq ▸ hj)
      by_cases lt : j<26
      · exact rowCover i ⟨j,lt⟩ (z j hj) ne
      · exact List.getD_eq_default _ _ (by simp [row,incidenceInput]; omega))
    have good := ok (kLine i) (kPoint i) (actual i)
    change C.eval (row i) = true at good
    rw [runEq C _ (by simp [row,incidenceInput])] at good
    change execute 26 C.gates (pullList (row i)) C.output = false at bad
    rw [bad] at good
    contradiction
  have cc : crit.card=19 := by decide
  have cnt := Finset.card_le_card sub
  omega

theorem commonOrFloor (C D : Circuit) (eq : C.gates=D.gates) (mc : Monotone2 C)
    (pos : RightOnIncidentPairs lines C) (pos' : RightOnIncidentPairs lines D)
    (dis : Disjoint ((quadrangles lines).filter fun q => C.eval (incidenceInput q (missLines lines q))=true)
      ((quadrangles lines).filter fun q => D.eval (incidenceInput q (missLines lines q))=true)) :
    18 ≤ (C.gates.map charge).sum := by
  by_cases hc : C.eval base=false
  · exact charged C mc pos hc
  · have ca : C.eval base=true := by cases h : C.eval base <;> simp_all
    have nd : D.eval base=false := by
      by_contra! hn
      have da : D.eval base=true := by cases h : D.eval base <;> simp_all
      exact Finset.disjoint_left.mp dis (Finset.mem_filter.mpr ⟨qArc,ca⟩) (Finset.mem_filter.mpr ⟨qArc,da⟩)
    rw [eq]
    exact charged D (fun g hg => mc g (eq.symm ▸ hg)) pos' nd

theorem chargedOnRow (C : Circuit) (mc : Monotone2 C) (ok : RightOnIncidentPairs lines C)
    (fail : C.eval base = false) : 18 ≤ zeroCharge 26 C.gates (pullList base) := by
  classical
  have bl : base.length=26 := by simp [base,incidenceInput]
  rw [runEq C base bl] at fail
  obtain ⟨S,sz,z,keep⟩ := fullZeroOnRow C.gates 26 C.output (pullList base)
    (fun g hg => ⟨by
      rcases (mc g hg).1 with h | h
      · exact Or.inl h
      · exact Or.inr h, (mc g hg).2⟩) fail
  have sub : crit ⊆ S := by
    rw [allPins]
    intro v hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    by_contra hi
    have bad := keep (pullList (row i)) (by
      intro j hj
      have ne : j≠kPin i := fun eq => hi (eq ▸ hj)
      by_cases lt : j<26
      · exact rowCover i ⟨j,lt⟩ (z j hj) ne
      · exact List.getD_eq_default _ _ (by simp [row,incidenceInput]; omega))
    have good := ok (kLine i) (kPoint i) (actual i)
    change C.eval (row i) = true at good
    rw [runEq C _ (by simp [row,incidenceInput])] at good
    change execute 26 C.gates (pullList (row i)) C.output = false at bad
    rw [bad] at good
    contradiction
  have cc : crit.card=19 := by decide
  have cnt := Finset.card_le_card sub
  omega

theorem commonOrOnRow (C D : Circuit) (eq : C.gates=D.gates) (mc : Monotone2 C)
    (pos : RightOnIncidentPairs lines C) (pos' : RightOnIncidentPairs lines D)
    (dis : Disjoint ((quadrangles lines).filter fun q => C.eval (incidenceInput q (missLines lines q))=true)
      ((quadrangles lines).filter fun q => D.eval (incidenceInput q (missLines lines q))=true)) :
    18 ≤ zeroCharge 26 C.gates (pullList base) := by
  by_cases hc : C.eval base=false
  · exact chargedOnRow C mc pos hc
  · have ca : C.eval base=true := by cases h : C.eval base <;> simp_all
    have nd : D.eval base=false := by
      by_contra! hn
      have da : D.eval base=true := by cases h : D.eval base <;> simp_all
      exact Finset.disjoint_left.mp dis (Finset.mem_filter.mpr ⟨qArc,ca⟩) (Finset.mem_filter.mpr ⟨qArc,da⟩)
    rw [eq]
    exact chargedOnRow D (fun g hg => mc g (eq.symm ▸ hg)) pos' nd

end PEqualNP.Outside.L_meta_17661

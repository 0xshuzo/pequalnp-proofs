import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9248.Escape

open PEqualNP.ProofComplexity PEqualNP.Search

variable {V : Type} [DecidableEq V]

def replay (db : List (List (Literal V))) (fs : List (Literal V)) : List Nat → Bool
  | [] => false
  | i :: trail =>
    match db[i]? with
    | none => false
    | some d =>
      match d.filter (fun l => !fs.contains l) with
      | [] => true
      | [l] => replay db (negLit l :: fs) trail
      | _ => false

theorem replay_sound (db : List (List (Literal V))) (Γ : Set (Clause V))
    (A : Set (Literal V)) (hd : ∀ d ∈ db, d.toFinset ∈ Γ)
    (trail : List Nat) (fs : List (Literal V))
    (hf : ∀ l ∈ fs, UPForces Γ A (negLit l)) (h : replay db fs trail = true) :
    ∃ D ∈ Γ, ∀ l ∈ D, UPForces Γ A (negLit l) := by
  induction trail generalizing fs with
  | nil => simp [replay] at h
  | cons i trail ih =>
    simp only [replay] at h
    split at h
    · contradiction
    next d he =>
      have hm := hd d (List.mem_of_getElem? he)
      split at h
      next hnil =>
        refine ⟨d.toFinset, hm, ?_⟩
        intro l hl
        have hld : l ∈ d := List.mem_toFinset.mp hl
        apply hf
        by_contra hn
        have : l ∈ d.filter (fun l => !fs.contains l) := by simp [hld, hn]
        rw [hnil] at this
        exact List.not_mem_nil this
      next l hsingle =>
        have hld : l ∈ d.filter (fun v => !fs.contains v) := by
          rw [hsingle]
          exact List.mem_cons_self
        have hu : UPForces Γ A l := by
          apply UPForces.unit hm (List.mem_toFinset.mpr (List.mem_filter.mp hld).1)
          intro v hv hne
          apply hf
          by_contra hn
          have hvd : v ∈ d := List.mem_toFinset.mp hv
          have : v ∈ d.filter (fun x => !fs.contains x) := by simp [hvd, hn]
          rw [hsingle] at this
          exact hne (List.mem_singleton.mp this)
        apply ih (negLit l :: fs) _ h
        intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · simpa [negLit] using hu
        · exact hf v hv
      next => contradiction

def verify (db : List (List (Literal V))) :
    List (List (Literal V) × List Nat) → Bool
  | [] => true
  | (c, trail) :: steps => replay db c trail && verify (db ++ [c]) steps

def learned (s : List (List (Literal V) × List Nat)) (ρ : List (Clause V)) :=
  s.foldl (fun acc p => p.1.toFinset :: acc) ρ

theorem verify_sound (F : Set (Clause V)) (steps : List (List (Literal V) × List Nat))
    (db : List (List (Literal V))) (ρ : List (Clause V)) (hr : IsRUPRun F ρ)
    (hd : ∀ d ∈ db, d.toFinset ∈ F ∪ {D | D ∈ ρ}) (h : verify db steps = true) :
    IsRUPRun F (learned steps ρ) := by
  induction steps generalizing db ρ with
  | nil => exact hr
  | cons head steps ih =>
    obtain ⟨c, trail⟩ := head
    have ⟨ht, hs⟩ := Bool.and_eq_true_iff.mp h
    have hc : IsRUP (F ∪ {D | D ∈ ρ}) c.toFinset := by
      apply replay_sound db _ _ hd trail c _ ht
      intro l hl
      exact UPForces.hyp ⟨l, List.mem_toFinset.mpr hl, rfl⟩
    apply ih (db ++ [c]) (c.toFinset :: ρ) (IsRUPRun.learn hr hc) _ hs
    intro d hmem
    rcases List.mem_append.mp hmem with hm | hm
    · rcases hd d hm with hF | hρ
      · exact Or.inl hF
      · exact Or.inr (List.mem_cons_of_mem _ hρ)
    · have he : d = c := by simpa using hm
      exact Or.inr (he ▸ List.mem_cons_self)

abbrev Board := Fin 5 × Fin 4

def row (p : Fin 5) : List (Literal Board) :=
  (List.finRange 4).map (fun h => ((p, h), true))

def block (p q : Fin 5) (h : Fin 4) : List (Literal Board) :=
  [((p, h), false), ((q, h), false)]

def input : List (List (Literal Board)) :=
  (List.finRange 5).map row ++ (List.finRange 4).flatMap (fun h =>
    (List.finRange 5).flatMap (fun p =>
      ((List.finRange 5).filter (fun q => p < q)).map (fun q => block p q h)))

theorem input_sound (d : List (Literal Board)) (hd : d ∈ input) :
    d.toFinset ∈ PHP 5 4 := by
  rcases List.mem_append.mp hd with hr | hb
  · obtain ⟨p, _, rfl⟩ := List.mem_map.mp hr
    left
    refine ⟨p, ?_⟩
    ext l
    simp [row]
  · obtain ⟨h, _, hh⟩ := List.mem_flatMap.mp hb
    obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp hh
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    right
    exact ⟨p, q, h, ne_of_lt (of_decide_eq_true (List.mem_filter.mp hq).2), by simp [block]⟩

def readLiteral (k : Nat) : Literal Board :=
  ((Fin.ofNat 5 (k / 2 / 4), Fin.ofNat 4 (k / 2)), decide (k % 2 = 0))

def offClause : Clause Board := {(((0,3):Board),false)}
def Fixed : Set (Clause Board) := PHP 5 4 ∪ {offClause}
def db := input ++ [[(((0,3):Board),false)]]
theorem dbLegal (d) (h : d∈db) : d.toFinset ∈ Fixed := by
  change d∈input++[_] at h
  rcases List.mem_append.mp h with raw|off
  · exact Or.inl (input_sound d raw)
  · obtain rfl := List.mem_singleton.mp off
    exact Or.inr rfl
def steps : List (List (Literal Board) × List Nat) := ([([15, 24, 26, 34],[35, 39, 40, 3, 27, 30, 32, 34, 41, 4, 8, 0, 11, 13, 2, 15, 16]),([4, 19],[16, 19, 22, 23, 45, 0, 5, 6, 7, 8, 46, 1, 29, 30, 3, 31, 4, 42, 44]),([3, 15],[15, 16, 17, 18, 35, 39, 40, 41, 46, 7, 10, 12, 2, 14, 4, 26, 29, 32, 33]),([3, 12, 20],[15, 16, 17, 18, 45, 48, 1, 5, 9, 2, 10, 11, 42, 3, 27, 34, 4, 43]),([29],[27, 30, 32, 34, 45, 47, 49, 0, 5, 6, 2, 7, 8, 39, 1, 20, 21, 4, 42, 43]),([3, 30],[15, 16, 17, 18, 45, 48, 50, 3, 7, 10, 1, 12, 14, 25, 29, 2, 31, 4, 43])] : List (List Nat × List Nat)).map (fun t => (t.1.map readLiteral,t.2))
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
theorem run : IsRUPRun Fixed (learned steps []) :=
  verify_sound _ _ _ _ IsRUPRun.nil (fun d h => Or.inl (dbLegal d h)) (by decide +kernel)
theorem count : (learned steps []).length=6 := by decide +kernel
def boards : Array (Nat × Nat) := #[(0, 8),(0, 9),(0, 12),(0, 4108),(0, 12296),(0, 12300),(0, 69644),(0, 77836),(0, 81932),(0, 143368),(0, 143372),(0, 208908),(0, 835592),(1, 86300),(2, 139821),(2, 143917),(2, 209453),(4, 279624),(4, 803912),(1152, 838476),(2112, 836796),(4096, 65817),(4098, 205629),(16384, 263244),(16384, 787532),(16384, 791628),(32769, 620956),(65536, 4377),(65538, 144189),(294912, 752844),(524288, 36040)]
def wk (v : Board) := 4*v.1.val+v.2.val
def undec (b : Nat × Nat) (l : Literal Board) := !((b.1 ||| b.2).testBit (wk l.1))
def holds (b : Nat × Nat) (l : Literal Board) :=
  (if l.2 then b.1 else b.2).testBit (wk l.1)
def singled (b : Nat × Nat) (c : List (Literal Board)) :=
  !(c.any (holds b)) && (c.filter (undec b)).length == 1
theorem sixEscape : ∀ k : Fin 31, steps.any (fun t => singled (boards[k.val]!) t.1)=true := by
  decide +kernel
end PEqualNP.Outside.L_meta_9248.Escape

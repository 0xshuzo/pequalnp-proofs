import PEqualNP.Outside.L_meta_4510
import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_2006
import PEqualNP.Outside.L_meta_2880
import PEqualNP.Outside.L_meta_3771
import PEqualNP.Outside.L_meta_3777

namespace Tests3774

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

abbrev I := Fin 13
abbrev V := Fin (13+13)
def D : Finset I := {0,1,3,9}
def incident (p l : I) : Prop := p+l ∈ D
instance (p l : I) : Decidable (incident p l) := inferInstanceAs (Decidable (p+l∈D))
def pts (x : V → Bool) : Finset I := Finset.univ.filter (fun i => x (i.castAdd 13) = true)
def lines (x : V → Bool) : Finset I := Finset.univ.filter (fun i => x (Fin.natAdd 13 i) = true)
def flag (x : V → Bool) := ∃ p l : I, incident p l ∧ x (p.castAdd 13)=true ∧ x (Fin.natAdd 13 l)=true

def upper (P : Finset I) : V → Bool := Fin.addCases (motive := fun _ => Bool)
  (fun p => decide (p ∈ P)) (fun l => decide (∀ p ∈ P, ¬incident p l))
def lower (L : Finset I) : V → Bool := Fin.addCases (motive := fun _ => Bool)
  (fun p => decide (∀ l ∈ L, ¬incident p l)) (fun l => decide (l ∈ L))

theorem upLine (S : Finset I) (l : I) :
    upper S (Fin.natAdd 13 l) = decide (∀ p∈S, ¬incident p l) := Fin.addCases_right l

theorem lowLine (S : Finset I) (l : I) :
    lower S (Fin.natAdd 13 l) = decide (l∈S) := Fin.addCases_right l

theorem exact (C : Circuit) (hm : Monotone2 C)
    (good : ∀ p l : I, incident p l → C.eval (List.ofFn (pairInput (p.castAdd 13) (Fin.natAdd 13 l)))=true)
    (bad : ∀ T : Finset I, T.card≤3 → C.eval (List.ofFn (upper T))=false ∧ C.eval (List.ofFn (lower T))=false) :
    ∀ x : V → Bool, C.eval (List.ofFn x)=true ↔ flag x := by
  intro x
  have pm (p : I) : p ∈ pts x ↔ x (p.castAdd 13) = true := by simp [pts]
  have lm (l : I) : l ∈ lines x ↔ x (Fin.natAdd 13 l) = true := by simp [lines]
  constructor
  · intro yes 
    by_contra absent
    have dis : ∀ p∈pts x, ∀ l∈lines x, ¬incident p l :=
      fun p hp l hl e => absent ⟨p,l,e,(pm p).mp hp,(lm l).mp hl⟩
    rcases PEqualNP.Outside.L_meta_3771 (pts x) (lines x) dis with small|small
    · have le : x ≤ upper (pts x) := by
        intro i
        induction i using Fin.addCases with
        | left p => apply Bool.le_iff_imp.mpr; intro hp; simpa [upper] using (pm p).mpr hp
        | right l =>
          apply Bool.le_iff_imp.mpr
          intro hl
          simpa only [upLine,decide_eq_true_eq] using (fun p hp => dis p hp l ((lm l).mpr hl))
      have z := PEqualNP.Outside.L_meta_2880.cmono C hm 26 _ _ le yes
      rw [(bad _ small).1] at z
      contradiction
    · have le : x ≤ lower (lines x) := by
        intro i
        induction i using Fin.addCases with
        | left p =>
          apply Bool.le_iff_imp.mpr
          intro hp
          simpa [lower] using (fun l hl => dis p ((pm p).mpr hp) l hl)
        | right l => apply Bool.le_iff_imp.mpr; intro hl; simpa only [lowLine,decide_eq_true_eq] using (lm l).mpr hl
      have z := PEqualNP.Outside.L_meta_2880.cmono C hm 26 _ _ le yes
      rw [(bad _ small).2] at z
      contradiction
  · rintro ⟨p,l,hl,hp,hq⟩
    apply PEqualNP.Outside.L_meta_2880.cmono C hm 26 _ _ _ (good p l hl)
    intro i
    apply Bool.le_iff_imp.mpr
    intro hi
    rcases of_decide_eq_true hi with rfl|rfl
    · exact hp
    · exact hq

end Tests3774

namespace HeadErase3774

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3777

def drop (n : ℕ) (tail : List Gate) (out : ℕ) : Circuit :=
  ⟨tail.map (aliasGate n (n+tail.length)), aliasWire n (n+tail.length) out⟩

theorem transport (n : ℕ) (gs : List Gate) (out : ℕ) (v : List Bool) (len : v.length=n) :
    (drop n gs out).eval v = (gs.foldl stepWire (v++[false])).getD out false := by
  let far := n+gs.length
  have read (U V : List Bool) (m : wiresMatch v false U V) (lt : V.length ≤ far) (u : ℕ) :
      V.getD (aliasWire n far u) false = U.getD u false := by
    by_cases eq : u=n
    · subst u
      rw [aliasWire,if_pos rfl,getD_ge_length _ _ lt]
      exact (len ▸ m.2.2.1).symm
    · rw [aliasWire,if_neg eq,←len]
      exact wiresMatch_getD_shiftDown m (by omega)
  have hm := foldl_wiresMatch v false gs (gs.map (aliasGate n far)) (v++[false]) v
    (wiresMatch_init v false) (by simp) (by
      intro i hi hj U V m lenV
      simp only [List.getElem_map,aliasGate,List.map_map]
      congr 1
      exact List.map_congr_left fun u _ => read U V m (by dsimp [far]; omega) u)
  apply read _ _ hm
  rw [foldl_stepWire_length,List.length_map]
  dsimp only [far]
  omega

theorem legal {g : Gate} {gs : List Gate} {out n : ℕ} (hm : Monotone2 ⟨g::gs,out⟩) :
    Monotone2 (drop n gs out) := by
  intro z hz
  obtain ⟨old,ho,rfl⟩ := List.mem_map.mp hz
  simpa [aliasGate] using hm old (List.mem_cons_of_mem g ho)

theorem sub (g : Gate) (gs : List Gate) (out n : ℕ) (hm : Monotone2 ⟨g::gs,out⟩)
    (v : List Bool) (len : v.length=n) (on : (drop n gs out).eval v=true) :
    (⟨g::gs,out⟩ : Circuit).eval v=true := by
  let b := g.op.eval (g.inputs.map fun i => v.getD i false)
  have ordered (i : ℕ) : (v++[false]).getD i false=true → (v++[b]).getD i false=true := by
    rcases Nat.lt_trichotomy i v.length with h|h|h
    · rw [PEqualNP.Outside.L_meta_2880.getD_snoc_lt _ _ _ h,PEqualNP.Outside.L_meta_2880.getD_snoc_lt _ _ _ h]
      exact id
    · subst i
      simp
    · rw [PEqualNP.Outside.L_meta_2880.getD_snoc_gt _ _ _ h]
      simp
  rw [transport n gs out v len] at on
  apply PEqualNP.Outside.L_meta_2880.mono2 gs _ (v++[false]) (v++[b]) (by simp) ordered out on
  intro a ha
  obtain ⟨op,arity⟩ := hm a (List.mem_cons_of_mem g ha)
  exact ⟨op,arity⟩

theorem equal_when_off (g : Gate) (gs : List Gate) (out n : ℕ) (v : List Bool) (len : v.length=n)
    (off : g.op.eval (g.inputs.map fun i => v.getD i false)=false) :
    (drop n gs out).eval v=(⟨g::gs,out⟩ : Circuit).eval v := by
  rw [transport n gs out v len]
  change (gs.foldl stepWire (v++[false])).getD out false =
    (gs.foldl stepWire (v++[g.op.eval (g.inputs.map fun i => v.getD i false)])).getD out false
  rw [off]

theorem dropHead (n : ℕ) (g : Gate) (gs : List Gate) (out : ℕ)
    (hm : Monotone2 ⟨g::gs,out⟩) (positive negative : (Fin n → Bool) → Prop)
    (dead : ∀ x, positive x → g.op.eval (g.inputs.map fun i => (List.ofFn x).getD i false)=false)
    (pos : ∀ x, positive x → (⟨g::gs,out⟩ : Circuit).eval (List.ofFn x)=true)
    (neg : ∀ x, negative x → (⟨g::gs,out⟩ : Circuit).eval (List.ofFn x)=false) :
    ∃ E : Circuit, Monotone2 E ∧ E.size=gs.length ∧
      (∀ x, positive x → E.eval (List.ofFn x)=true) ∧ (∀ x, negative x → E.eval (List.ofFn x)=false) := by
  refine ⟨drop n gs out,legal hm,by simp [drop,Circuit.size],?_,?_⟩
  · intro x hx
    rw [equal_when_off _ _ _ _ _ List.length_ofFn (dead x hx)]
    exact pos x hx
  · intro x hx
    cases h : (drop n gs out).eval (List.ofFn x) with
    | false => rfl
    | true =>
      have hi := sub _ _ _ _ hm _ List.length_ofFn h
      rw [neg x hx] at hi
      contradiction

end HeadErase3774

namespace Rename3774

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2880

def wire {n : ℕ} (σ : Fin n → Fin n) (w : ℕ) :=
  if h : w<n then (σ ⟨w,h⟩).val else w
def gate {n : ℕ} (σ : Fin n → Fin n) (g : Gate) : Gate := ⟨g.op,g.inputs.map (wire σ)⟩
def circ {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) : Circuit := ⟨C.gates.map (gate σ),wire σ C.output⟩

theorem below {n : ℕ} (σ : Fin n → Fin n) (len i : ℕ) (range : n≤len) (h : i<len) :
    wire σ i < len := by
  unfold wire
  split
  next hw => exact Nat.lt_of_lt_of_le (σ ⟨i,hw⟩).isLt range
  next => exact h

theorem keep {n : ℕ} (σ : Fin n → Fin n) (gs : List Gate) (W V : List Bool)
    (eq : W.length=V.length) (range : n≤V.length)
    (sync : ∀ i, W.getD (wire σ i) false=V.getD i false) :
    ∀ i, (wf (gs.map (gate σ)) W).getD (wire σ i) false=(wf gs V).getD i false := by
  induction gs generalizing W V with
  | nil => exact sync
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => V.getD i false)
    have same : (gate σ g).op.eval ((gate σ g).inputs.map fun i => W.getD i false)=b := by
      change g.op.eval ((g.inputs.map (wire σ)).map _) = g.op.eval _
      congr 1
      rw [List.map_map]
      exact List.map_congr_left fun i _ => sync i
    intro w
    simp only [List.map_cons,wf,List.foldl_cons] at ⊢
    rw [same]
    apply ih (W++[b]) (V++[b]) (by simpa using eq) (by simp; omega) _ w
    intro i
    rcases Nat.lt_trichotomy i V.length with lt|atEnd|gt
    · rw [getD_snoc_lt W b _ (by rw [eq]; exact below σ V.length i range lt),getD_snoc_lt V b _ lt]
      exact sync i
    · subst i
      have hi : ¬V.length<n := by omega
      rw [wire,dif_neg hi,←eq,getD_snoc_eq]
      rw [eq,getD_snoc_eq]
    · have hi : ¬i<n := by omega
      rw [wire,dif_neg hi,getD_snoc_gt W b _ (by omega),getD_snoc_gt V b _ gt]

theorem eval {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
    (circ σ C).eval (List.ofFn x)=C.eval (List.ofFn (x ∘ σ)) := by
  apply keep σ C.gates _ _ (by simp) (by simp)
  intro i
  by_cases hi : i<n
  · simp [wire,hi,List.getD_eq_getElem?_getD,(σ ⟨i,hi⟩).isLt,Function.comp]
  · simp only [wire,dif_neg hi]
    rw [List.getD_eq_default _ _ (by simp; omega),List.getD_eq_default _ _ (by simp; omega)]

theorem legal {n : ℕ} (σ : Fin n → Fin n) (C : Circuit) (hm : Monotone2 C) :
    Monotone2 (circ σ C) := by
  intro g hg
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hg
  simpa [gate] using hm a ha

end Rename3774
namespace Symmetry3774
abbrev V := Fin 26

def edge (p q : V) : Bool := decide ((p.val<13) ≠ (q.val<13)) &&
  [0,1,3,9].contains ((p.val+q.val)%13)

def step (k : ℕ) (x : V) : V :=
  ([[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25],[1,2,3,4,5,6,7,8,9,10,11,12,0,25,13,14,15,16,17,18,19,20,21,22,23,24],[0,3,6,9,12,2,5,8,11,1,4,7,10,13,16,19,22,25,15,18,21,24,14,17,20,23],[1,0,2,3,8,5,7,6,4,9,12,11,10,13,25,16,15,17,18,23,20,22,21,19,24,14],[13,14,15,16,17,18,19,20,21,22,23,24,25,0,1,2,3,4,5,6,7,8,9,10,11,12],[12,0,1,2,3,4,5,6,7,8,9,10,11,14,15,16,17,18,19,20,21,22,23,24,25,13],[0,9,5,1,10,6,2,11,7,3,12,8,4,13,22,18,14,23,19,15,24,20,16,25,21,17]] : List (List V))[k]?.getD [] |>.getD x.val x

def action : ℕ → ℕ → V → V
 | 0,_,x => x
 | depth+1,w,x => action depth (w/8) (step (w%8) x)

theorem step_inj : ∀ (k : Fin 8) (x y : V), step k x=step k y → x=y := by decide +kernel
theorem step_geom : ∀ (k : Fin 8) (x y : V), edge (step k x) (step k y)=edge x y := by decide +kernel

theorem sound (depth w : ℕ) : Function.Bijective (action depth w) ∧
    ∀ x y, edge (action depth w x) (action depth w y)=edge x y := by
  induction depth generalizing w with
  | zero => exact ⟨Function.bijective_id,fun _ _ => rfl⟩
  | succ depth ih =>
    let k : Fin 8 := ⟨w%8,Nat.mod_lt _ (by decide)⟩
    have inject : Function.Injective (step k) := fun a b h => step_inj k a b h
    refine ⟨(ih (w/8)).1.comp ⟨inject,Finite.surjective_of_injective inject⟩,?_⟩
    intro x y
    exact ((ih (w/8)).2 (step k x) (step k y)).trans (step_geom k x y)

def code (a b : V) : ℕ :=
  ([[0,0,43,6,202,346,350,1226,153,2,206,1230,25,0,25,9,206,90,74,78,5982,2771,202,94,747,11],
  [3,0,5,51,53,1621,2773,2803,1619,19,21,1653,1651,3,1,1651,75,42,595,755,8942,1619,346,627,93,5],
  [235,29,0,45,413,369,2969,11161,3307,5209,157,173,241,0,235,345,341,113,6045,5995,2969,2773,3274,749,45,29],
  [30,158,237,0,174,3309,46,371,1395,414,651,1261,81,30,43,115,14,5022,6046,371,666,4851,606,46,237,5],
  [10,245,1269,94,0,394,3166,138,595,922,1675,5035,1118,349,17,117,5466,22411,595,651,8858,4853,10,94,45,245],
  [683,85,1905,10097,757,0,2954,23635,1109,234,3306,5017,1258,2,49,3273,3278,234,2762,1395,11102,85,683,174,1905,395],
  [1886,5323,685,238,1262,6001,0,1390,4851,366,1877,13387,627,6,409,1369,1877,3162,8913,2766,366,4851,394,238,1387,21],
  [665,6042,5483,593,606,8798,750,0,1102,666,78,1673,13513,51,171,1673,5322,1114,22133,78,666,2906,606,5321,173,53],
  [1689,83,1233,755,74,746,1107,5770,0,938,5333,629,209,414,209,4817,939,2801,74,755,1390,83,665,81,363,139],
  [26,211,669,154,5214,42,1902,8861,2974,0,426,11166,113,26,602,2803,350,42,2974,371,669,83,10,46,1117,3317],
  [14,11,395,926,139,8793,341,1614,9806,601,0,73,7369,715,2460,587,14,601,938,926,669,85,138,4747,6027,11],
  [921,117,93,670,5771,1117,1099,137,721,6046,75,0,9,410,713,9,75,426,721,5357,685,1109,1370,1118,93,5707],
  [1,115,49,749,2769,2801,8941,1225,17,90,1114,201,0,89,1,115,73,90,721,593,366,1107,683,749,753,3285],
  [4,35,76,286,724,596,614,4915,5795,282,739,5980,92,0,4,307,38,282,2458,2291,1306,163,20,286,1310,35],
  [28,12,2283,604,266,4764,6044,37987,2257,282,5020,737,33,28,0,33,412,305,2257,19665,10475,5795,156,161,2283,7395],
  [4,1843,285,819,821,48353,42659,18057,2257,17099,267,265,225,1843,225,0,265,3297,2165,18057,23779,26419,41676,1249,1289,1845],
  [230,35,924,102,18059,19690,2972,5332,6571,2137,270,1801,33,230,1254,1801,0,1294,17323,270,2972,11164,3302,5212,9993,652],
  [281,140,817,2462,10334,2282,5212,17050,17097,84,742,265,1841,84,1841,5939,742,0,2474,25318,1108,2282,7380,13404,10474,8934],
  [20,163,19697,26214,1802,2282,11164,18058,673,5468,1294,5917,2138,5468,673,14453,47513,5937,0,17322,37662,8865,1802,5918,5917,5387],
  [38,3276,10956,819,2142,52307,2286,2126,17139,1306,739,11100,161,819,42588,5385,1806,8931,39325,0,10318,17139,2126,14417,4707,739],
  [412,1372,6553,5402,8916,18289,614,4915,10449,4838,2443,1289,305,5324,6553,37987,4748,4838,38686,4915,0,8806,5332,614,13388,13597],
  [3302,1676,19691,2291,2293,596,6044,10318,668,675,652,2165,1116,1699,668,9868,6044,596,2131,8860,39321,0,4890,42657,4913,1676],
  [212,4820,2461,286,266,4771,2972,5345,668,84,270,8929,5219,212,1692,5345,1236,4771,266,14414,46362,17141,0,2442,39307,821],
  [798,307,2289,102,2142,6538,2286,5345,673,1108,1291,17054,92,102,92,3164,7398,1116,10334,2129,2286,10478,2142,0,588,19550],
  [2457,797,76,604,2442,5772,42761,5385,8865,10329,8934,737,6385,7372,611,737,5350,46172,8929,4835,1100,5772,46179,604,0,76],
  [99,12,285,588,724,5772,4748,2126,2131,2259,267,5899,10330,12,924,309,267,2443,18059,1291,1309,140,724,8916,285,0]] : List (List ℕ))[a.val]?.getD [] |>.getD b.val 0
def align (a b : V) := action 6 (code a b)

def shape (a b : V) : Prop :=
    ((align a b a=0 ∧ align a b b=1) ∨ (align a b a=0 ∧ align a b b=13) ∨
      (align a b a=2 ∧ align a b b=13)) ∧
    (edge a b=true → align a b a=0 ∧ align a b b=13)
instance (a b : V) : Decidable (shape a b) := by unfold shape; infer_instance
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
theorem row0 : ∀ b : V, 0≠b → shape 0 b := by decide +kernel
theorem row1 : ∀ b : V, 1≠b → shape 1 b := by decide +kernel
theorem row2 : ∀ b : V, 2≠b → shape 2 b := by decide +kernel
theorem row3 : ∀ b : V, 3≠b → shape 3 b := by decide +kernel
theorem row4 : ∀ b : V, 4≠b → shape 4 b := by decide +kernel
theorem row5 : ∀ b : V, 5≠b → shape 5 b := by decide +kernel
theorem row6 : ∀ b : V, 6≠b → shape 6 b := by decide +kernel
theorem row7 : ∀ b : V, 7≠b → shape 7 b := by decide +kernel
theorem row8 : ∀ b : V, 8≠b → shape 8 b := by decide +kernel
theorem row9 : ∀ b : V, 9≠b → shape 9 b := by decide +kernel
theorem row10 : ∀ b : V, 10≠b → shape 10 b := by decide +kernel
theorem row11 : ∀ b : V, 11≠b → shape 11 b := by decide +kernel
theorem row12 : ∀ b : V, 12≠b → shape 12 b := by decide +kernel
theorem row13 : ∀ b : V, 13≠b → shape 13 b := by decide +kernel
theorem row14 : ∀ b : V, 14≠b → shape 14 b := by decide +kernel
theorem row15 : ∀ b : V, 15≠b → shape 15 b := by decide +kernel
theorem row16 : ∀ b : V, 16≠b → shape 16 b := by decide +kernel
theorem row17 : ∀ b : V, 17≠b → shape 17 b := by decide +kernel
theorem row18 : ∀ b : V, 18≠b → shape 18 b := by decide +kernel
theorem row19 : ∀ b : V, 19≠b → shape 19 b := by decide +kernel
theorem row20 : ∀ b : V, 20≠b → shape 20 b := by decide +kernel
theorem row21 : ∀ b : V, 21≠b → shape 21 b := by decide +kernel
theorem row22 : ∀ b : V, 22≠b → shape 22 b := by decide +kernel
theorem row23 : ∀ b : V, 23≠b → shape 23 b := by decide +kernel
theorem row24 : ∀ b : V, 24≠b → shape 24 b := by decide +kernel
theorem row25 : ∀ b : V, 25≠b → shape 25 b := by decide +kernel
theorem classify (a b : V) (ne : a≠b) : shape a b := by
  fin_cases a
  · exact row0 b ne
  · exact row1 b ne
  · exact row2 b ne
  · exact row3 b ne
  · exact row4 b ne
  · exact row5 b ne
  · exact row6 b ne
  · exact row7 b ne
  · exact row8 b ne
  · exact row9 b ne
  · exact row10 b ne
  · exact row11 b ne
  · exact row12 b ne
  · exact row13 b ne
  · exact row14 b ne
  · exact row15 b ne
  · exact row16 b ne
  · exact row17 b ne
  · exact row18 b ne
  · exact row19 b ne
  · exact row20 b ne
  · exact row21 b ne
  · exact row22 b ne
  · exact row23 b ne
  · exact row24 b ne
  · exact row25 b ne
end Symmetry3774
namespace Bridge3774

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open Tests3774
abbrev Vertex := Fin 26
def E (x : Vertex → Bool) : Prop := ∃ a b : Vertex, Symmetry3774.edge a b=true ∧ x a=true ∧ x b=true
def Rep (C : Circuit) := ∀ x, circuitFun 26 C x=true ↔ E x
def First (g : Gate) : Prop := (g.op=.and ∧ g.inputs=[0,13]) ∨
  (g.op=.or ∧ g.inputs∈[[0,1],[0,13],[2,13]])
def HasFirst (C : Circuit) := ∃ g, C.gates.head?=some g ∧ First g

theorem geometrical (x : Vertex → Bool) : E x ↔ flag x := by
  have forwards : ∀ p l : Fin 13, incident p l → Symmetry3774.edge (p.castAdd 13) (Fin.natAdd 13 l)=true := by decide +kernel
  have backwards : ∀ u v : Vertex, Symmetry3774.edge u v=true →
      ∃ p l : Fin 13, incident p l ∧
        ((u=p.castAdd 13 ∧ v=Fin.natAdd 13 l) ∨ (v=p.castAdd 13 ∧ u=Fin.natAdd 13 l)) := by decide +kernel
  constructor
  · rintro ⟨u,v,edge,hu,hv⟩
    obtain ⟨p,l,h,⟨rfl,rfl⟩|⟨rfl,rfl⟩⟩ := backwards u v edge
    · exact ⟨p,l,h,hu,hv⟩
    · exact ⟨p,l,h,hv,hu⟩
  · rintro ⟨p,l,h,hp,hl⟩
    exact ⟨_,_,forwards p l h,hp,hl⟩

theorem renPres (σ : Vertex → Vertex) (onto : Function.Surjective σ)
    (pres : ∀ a b, Symmetry3774.edge (σ a) (σ b) = Symmetry3774.edge a b) (x : Vertex → Bool) :
    E (x ∘ σ) ↔ E x := by
  constructor
  · rintro ⟨u,v,e,hu,hv⟩
    exact ⟨σ u,σ v,(pres u v).trans e,hu,hv⟩
  · rintro ⟨u,v,e,hu,hv⟩
    obtain ⟨a,rfl⟩ := onto u
    obtain ⟨b,rfl⟩ := onto v
    exact ⟨a,b,(pres a b).symm.trans e,hu,hv⟩

theorem on_pair {a b : Vertex} (e : Symmetry3774.edge a b=true) : E (pairInput a b) :=
  ⟨a,b,e,by simp [pairInput],by simp [pairInput]⟩

theorem no_empty : ¬E (fun _ => false) := by
  rintro ⟨_,_,_,h,_⟩
  contradiction

theorem nonconst (C : Circuit) (rep : Rep C) :
    ∃ x y, circuitFun 26 C x ≠ circuitFun 26 C y := by
  refine ⟨pairInput 0 13,fun _ => false,?_⟩
  intro eq
  have full := (rep _).mpr (on_pair (a:=0) (b:=13) (by decide))
  rw [eq] at full
  exact no_empty ((rep _).mp full)

theorem nonempty (C : Circuit) (rep : Rep C) (valid : C.output<26+C.size) : C.gates≠[] := by
  intro empty
  obtain ⟨gs,out⟩ := C
  change gs=[] at empty
  subst gs
  have ho : out<26 := by simpa [Circuit.size] using valid
  let q : Vertex := ⟨out,ho⟩
  have get (x : Vertex → Bool) : circuitFun 26 ⟨[],out⟩ x = x q := by
    change (List.ofFn x).getD out false=_
    simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,ho,↓reduceDIte,Option.getD_some,q]
  have a := (rep _).mpr (on_pair (a:=0) (b:=13) (by decide))
  have b := (rep _).mpr (on_pair (a:=1) (b:=15) (by decide))
  rw [get] at a b
  have no : ∀ t : Vertex, ¬(pairInput (0:Vertex) 13 t=true ∧ pairInput (1:Vertex) 15 t=true) := by decide
  exact no q ⟨a,b⟩

theorem badgate_off (a b p l : Vertex) (ne : a≠b) (bad : Symmetry3774.edge a b≠true)
    (good : Symmetry3774.edge p l=true) :
    GateOp.and.eval [pairInput p l a,pairInput p l b]=false := by
  have sym : ∀ u v : Vertex, Symmetry3774.edge u v=Symmetry3774.edge v u := by decide +kernel
  cases ha : pairInput p l a <;> cases hb : pairInput p l b <;> try rfl
  have ha' : a=p ∨ a=l := of_decide_eq_true ha
  have hb' : b=p ∨ b=l := of_decide_eq_true hb
  exfalso
  rcases ha' with rfl|rfl <;> rcases hb' with rfl|rfl
  · exact ne rfl
  · exact bad good
  · exact bad ((sym _ _).trans good)
  · exact ne rfl

theorem reduceBad (g : Gate) (gs : List Gate) (out : ℕ) (a b : Vertex)
    (hm : Monotone2 ⟨g::gs,out⟩) (rep : Rep ⟨g::gs,out⟩) (op : g.op=.and) (inputs : g.inputs=[a.val,b.val])
    (ne : a≠b) (bad : Symmetry3774.edge a b≠true) :
    ∃ T : Circuit, Monotone2 T ∧ T.size=gs.length ∧ Rep T := by
  let T := HeadErase3774.drop 26 gs out
  refine ⟨T,HeadErase3774.legal hm,by simp [T,HeadErase3774.drop,Circuit.size],?_⟩
  intro x
  constructor
  · intro yes
    apply (rep x).mp
    exact HeadErase3774.sub _ _ _ _ hm _ List.length_ofFn yes
  · rintro ⟨p,l,inc,hp,hl⟩
    let y := pairInput p l
    have off : g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false)=false := by
      rw [op,inputs]
      have rd (i : Vertex) : (List.ofFn y).getD i.val false=y i := by
        simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,i.isLt,↓reduceDIte,Option.getD_some]
      simpa only [List.map_cons,List.map_nil,rd] using badgate_off a b p l ne bad inc
    have transfer := HeadErase3774.equal_when_off g gs out 26 (List.ofFn y) List.length_ofFn off
    have ey : T.eval (List.ofFn y)=true := transfer.trans ((rep y).mpr (on_pair inc))
    apply PEqualNP.Outside.L_meta_2880.cmono T (HeadErase3774.legal hm) 26 y x _ ey
    intro i
    apply Bool.le_iff_imp.mpr
    intro h
    rcases of_decide_eq_true h with rfl|rfl
    · exact hp
    · exact hl

theorem normalized (C : Circuit) (hc : Monotone2 C) (rep : Rep C) :
    ∃ T : Circuit, Monotone2 T ∧ T.size≤C.size ∧ Rep T ∧ HasFirst T := by
  obtain ⟨⟨gs,out⟩,hm,size,eq,valid,form⟩ := PEqualNP.Outside.L_meta_2006 26 C hc (nonconst C rep)
  have rd : Rep ⟨gs,out⟩ := fun x => (congrFun eq x).symm ▸ rep x
  cases gs with
  | nil => exact False.elim (nonempty _ rd valid rfl)
  | cons g gs =>
    obtain ⟨i,j,inputs,lt,hi⟩ := form 0 g (by rfl)
    let a : Vertex := ⟨i,by omega⟩
    let b : Vertex := ⟨j,by omega⟩
    have ne : a≠b := fun h => (Nat.ne_of_lt lt) (congrArg Fin.val h)
    by_cases good : Symmetry3774.edge a b=true
    all_goals
      let σ := Symmetry3774.align a b
      have sound := Symmetry3774.sound 6 (Symmetry3774.code a b)
      let C0 : Circuit := ⟨g::gs,out⟩
      let T := Rename3774.circ σ C0
      have rT : Rep T := fun x =>
        (show circuitFun 26 T x=circuitFun 26 C0 (x ∘ σ) from Rename3774.eval σ C0 x).symm ▸
          ((rd (x ∘ σ)).trans (renPres σ sound.1.surjective sound.2 x))
      have le : T.size≤C.size := by simpa [T,C0,Rename3774.circ,Circuit.size] using size
      have op := (hm g (List.mem_cons_self)).1
      have hform := Symmetry3774.classify a b ne
      change (((σ a=0 ∧ σ b=1) ∨ (σ a=0 ∧ σ b=13) ∨ (σ a=2 ∧ σ b=13)) ∧
        (Symmetry3774.edge a b=true → σ a=0 ∧ σ b=13)) at hform
      have renamed : (Rename3774.gate σ g).inputs=[(σ a).val,(σ b).val] := by
        simp [Rename3774.gate,inputs,Rename3774.wire,a,b,show i<26 by omega,show j<26 by omega]
    · obtain ⟨zero,line⟩ := hform.2 good
      refine ⟨T,Rename3774.legal σ C0 hm,le,rT,Rename3774.gate σ g,rfl,?_⟩
      rcases op with h|h
      · exact Or.inl ⟨h,by rw [renamed,zero,line] <;> decide⟩
      · refine Or.inr ⟨h,?_⟩
        simp [renamed,zero,line]
    · rcases op with h|h
      · obtain ⟨sm,hsm,sz,rs⟩ := reduceBad g gs out a b hm rd h inputs ne good
        obtain ⟨E,he,leE,rE,first⟩ := normalized sm hsm rs
        exact ⟨E,he,by change (g::gs).length ≤ C.size at size; simp at size; omega,rE,first⟩
      · refine ⟨T,Rename3774.legal σ C0 hm,le,rT,Rename3774.gate σ g,rfl,Or.inr ⟨h,?_⟩⟩
        rcases hform.1 with ⟨u,v⟩|⟨u,v⟩|⟨u,v⟩ <;> simp [renamed,u,v]
termination_by C.size
decreasing_by change (g::gs).length ≤ C.size at size; simp at size; omega

def Rows (C : Circuit) : Prop :=
  (∀ p l, incident p l → C.eval (List.ofFn (pairInput (p.castAdd 13) (Fin.natAdd 13 l)))=true) ∧
  (∀ T : Finset (Fin 13), T.card≤3 → C.eval (List.ofFn (upper T))=false ∧ C.eval (List.ofFn (lower T))=false)

theorem rows_iff (C : Circuit) (hm : Monotone2 C) : Rows C ↔ Rep C := by
  constructor
  · rintro ⟨pos,neg⟩ x
    exact (Tests3774.exact C hm pos neg x).trans (geometrical x).symm
  · intro rep
    constructor
    · intro p l edge
      apply (rep _).mpr
      apply (geometrical _).mpr
      exact ⟨p,l,edge,by simp [pairInput],by simp [pairInput]⟩
    · intro S _
      constructor
      · cases h : C.eval (List.ofFn (upper S)) with
        | false => rfl
        | true =>
          obtain ⟨p,l,e,hp,hl⟩ := (geometrical _).mp ((rep _).mp h)
          have inp : p ∈ S := by simpa [upper] using hp
          have ban : ∀ p ∈ S, ¬incident p l := by simpa only [upLine,decide_eq_true_eq] using hl
          exact False.elim (ban p inp e)
      · cases h : C.eval (List.ofFn (lower S)) with
        | false => rfl
        | true =>
          obtain ⟨p,l,e,hp,hl⟩ := (geometrical _).mp ((rep _).mp h)
          have inl : l ∈ S := by simpa only [lowLine,decide_eq_true_eq] using hl
          have ban : ∀ l ∈ S, ¬incident p l := by simpa [lower] using hp
          exact False.elim (ban l inl e)

theorem obstruction :
    (¬∃ C : Circuit, Monotone2 C ∧ C.size≤63 ∧ HasFirst C ∧ Rows C) ↔
      ∀ C : Circuit, Monotone2 C → Rep C → 64≤C.size := by
  constructor
  · intro no C hm rep
    by_contra! low
    obtain ⟨T,ht,sz,rt,f⟩ := normalized C hm rep
    exact no ⟨T,ht,by omega,f,(rows_iff T ht).mpr rt⟩
  · rintro lb ⟨C,hm,sz,_,rows⟩
    have h := lb C hm ((rows_iff C hm).mp rows)
    omega

theorem literal : (¬ (have x1 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; ∃ (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x2 ∧ x2.size ≤ (63 : ℕ) ∧ (∃ (x3 : PEqualNP.CircuitLowerBounds.Gate), x2.gates.head? = Option.some x3 ∧ (x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ x3.inputs = [(0 : ℕ), (13 : ℕ)] ∨ x3.op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ x3.inputs ∈ [[(0 : ℕ), (1 : ℕ)], [(0 : ℕ), (13 : ℕ)], [(2 : ℕ), (13 : ℕ)]])) ∧ (∀ (x3 x4 : Fin (13 : ℕ)), x3 + x4 ∈ x1 → x2.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput (Fin.castAdd (13 : ℕ) x3) (Fin.natAdd (13 : ℕ) x4))) = Bool.true) ∧ ∀ (x3 : Finset (Fin (13 : ℕ))), x3.card ≤ (3 : ℕ) → x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x7 + x6 ∉ x1)) x5) = Bool.false ∧ x2.eval (List.ofFn fun (x5 : Fin ((13 : ℕ) + (13 : ℕ))) => Fin.addCases (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (∀ x7 ∈ x3, x6 + x7 ∉ x1)) (fun (x6 : Fin (13 : ℕ)) => Decidable.decide (x6 ∈ x3)) x5) = Bool.false)) ↔ ∀ C : Circuit, Monotone2 C → Rep C → 64≤C.size := obstruction

end Bridge3774
namespace Bound3774
open Bridge3774 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4510_aux
open Symmetry3774

def G : SimpleGraph Vertex where
  Adj u v := edge u v=true
  symm := ⟨by decide +kernel⟩
  loopless := ⟨by decide +kernel⟩

instance : DecidableRel G.Adj := fun u v => inferInstanceAs (Decidable (edge u v=true))

theorem unrestricted (C : Circuit) (hm : Monotone2 C) (rep : Rep C) : 38 ≤ C.size := by
  have noSq : NoSq G := by
    have distinctN : ∀ u v : Vertex, u≠v → (Finset.univ.filter (fun t : Vertex => edge u t=true ∧ edge v t=true)).card ≤ 1 := by decide +kernel
    rintro a b c d ac bd ⟨ab,bc,cd,da⟩
    exact bd (Finset.card_le_one.mp (distinctN a c ac) b (Finset.mem_filter.mpr ⟨Finset.mem_univ _,ab,G.symm bc⟩)
      d (Finset.mem_filter.mpr ⟨Finset.mem_univ _,G.symm da,cd⟩))
  have degree (i : Vertex) : 2 ≤ (G.neighborSet i).ncard := by
    have existsTwo : ∀ i : Vertex, ∃ a b, edge i a=true ∧ edge i b=true ∧ a≠b := by decide +kernel
    obtain ⟨a,b,ha,hb,ne⟩ := existsTwo i
    exact (Set.one_lt_ncard_iff (s:=G.neighborSet i)).mpr ⟨a,ha,b,hb,ne⟩
  have coverMin (S : Finset Vertex) (coverS : CoverPromise.IsVertexCover G S) : 13≤S.card := by
    let P (i : Fin 13) := i.castAdd 13
    let Q (i : Fin 13) := Fin.natAdd 13 (-i)
    have flags : ∀ i : Fin 13, edge (P i) (Q i)=true := by decide +kernel
    let pick (i : Fin 13) := if P i∈S then P i else Q i
    have inside (i : Fin 13) : pick i∈S := by
      by_cases hi : P i∈S
      · simpa [pick,hi] using hi
      · simpa [pick,hi] using (coverS (P i) (Q i) (flags i)).resolve_left hi
    let back (x : Vertex) : Fin 13 := if x.val<13 then Fin.ofNat 13 x.val else -(Fin.ofNat 13 x.val)
    have inv : ∀ i : Fin 13, back (P i)=i ∧ back (Q i)=i := by decide +kernel
    have ret (i : Fin 13) : back (pick i)=i := by dsimp only [pick]; split <;> first | exact (inv i).1 | exact (inv i).2
    have inj : Function.Injective pick := fun a b e => (ret a).symm.trans ((congrArg back e).trans (ret b))
    have h := Finset.card_le_card_of_injOn (s:=Finset.univ) (t:=S) pick (fun i _ => inside i) inj.injOn
    simpa only [Finset.card_univ,Fintype.card_fin] using h
  have works : GraphEval C G := by
    intro u v
    change circuitFun 26 C (point {u,v})=true ↔ G.Adj u v
    rw [rep]
    constructor
    · rintro ⟨a,b,e,ha,hb⟩
      have ha' : a=u ∨ a=v := by simpa [point] using ha
      have hb' : b=u ∨ b=v := by simpa [point] using hb
      rcases ha' with rfl|rfl <;> rcases hb' with rfl|rfl
      · exact False.elim (G.loopless.irrefl _ e)
      · exact e
      · exact G.symm e
      · exact False.elim (G.loopless.irrefl _ e)
    · intro e
      exact ⟨u,v,e,by simp [point],by simp [point]⟩
  have h := min_two_bound noSq degree coverMin hm works
  omega
end Bound3774

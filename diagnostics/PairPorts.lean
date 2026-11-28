import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_166.PairPorts
abbrev V := Fin 5 × Fin 4
abbrev B := V → Bool
def words : Array Nat := #[541201,295441,533521,164881,272401,149521,540961,295201,532801,164161,270721,147841,529441,268321,528961,137281,266881,136321,99361,84001,98881,75841,82561,74881,540962,295202,529442,99362,268322,84002,541202,295442,528962,98882,266882,82562,533522,272402,532802,75842,270722,74882,164882,149522,164162,137282,147842,136322,532804,164164,528964,98884,137284,75844,533524,164884,529444,99364,136324,74884,541204,149524,540964,84004,147844,82564,295444,272404,295204,268324,270724,266884,270728,147848,266888,82568,136328,74888,272408,149528,268328,84008,137288,75848,295448,164888,295208,99368,164168,98888,541208,533528,540968,529448,532808,528968]
def sample (h q : Fin 4) (t : Fin 6) (v : V) : Bool :=
  words[24*h.val+6*q.val+t.val]!.testBit (4*v.1.val+v.2.val)
def fixed (x : B) (h : Fin 4) := ∀ k : Fin 4,x (0,k)=(h==k)
theorem sampleFixed : ∀h q t,fixed (sample h q t) h := by
  unfold fixed
  decide +kernel
open PEqualNP.ProofComplexity
abbrev C := Clause V
def key (q : Fin 4) : Fin 5 := ⟨q.val+1,by omega⟩
def extra (h i j : Fin 4) (l : Literal V) :=
    l.1.2=h ∧ l.2=true ∧ l.1.1≠key i ∧ l.1.1≠key j
def closedPort (h i j : Fin 4) (c : C) :=
    (∀t : Fin 6, ¬ ClauseSat (sample h i t) c) ∧ (∀t : Fin 6, ¬ ClauseSat (sample h j t) c)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem literalTable : ∀ (h i j : Fin 4),i≠j → ∀ l : Literal V,
    (∀t : Fin 6, sample h i t l.1 ≠ l.2) →
    (∀t : Fin 6, sample h j t l.1 ≠ l.2) → l.1.1=0 ∨ extra h i j l := by
  unfold extra
  decide +kernel

theorem portShape {c : C} {h i j : Fin 4} (ne : i≠j) (cl : closedPort h i j c)
    {l : Literal V} (hl : l∈c) : l.1.1=0 ∨ extra h i j l := by
  exact literalTable h i j ne l (fun t a=>cl.1 t ⟨l,hl,a⟩) (fun t a=>cl.2 t ⟨l,hl,a⟩)

theorem atPort {c : C} {h i j : Fin 4} (ne : i≠j) (cl : closedPort h i j c)
    (x : B) (hx : fixed x h) (empty : ∀ r : Fin 5,r≠0 → x (r,h)=false) : ¬ ClauseSat x c := by
  rintro ⟨l,hl,ev⟩
  by_cases p : l.1.1=0
  · apply cl.1 0
    refine ⟨l,hl,?_⟩
    have eq : l.1=(0,l.1.2) := Prod.ext p rfl
    rw [eq,show sample h i 0 (0,l.1.2)=(h==l.1.2) from sampleFixed h i 0 _]
    rw [eq,show x (0,l.1.2)=(_==l.1.2) from hx _] at ev
    exact ev
  · obtain e := (portShape ne cl hl).resolve_left p
    have eq : l.1=(l.1.1,h) := Prod.ext rfl e.1
    rw [eq,empty _ p,e.2.1] at ev
    contradiction

set_option maxRecDepth 4096 in
theorem escapeTable : ∀ (h k i j q : Fin 4),h≠k → i≠j →
    ∃ t : Fin 6, ∀ r : Fin 5, r≠0 → r≠key i → r≠key j → sample k q t (r,h)=false := by
  decide +kernel

theorem later {c : C} {h k i j q : Fin 4} (hk : h≠k) (ij : i≠j)
    (cl : closedPort h i j c) (safe : ∀t : Fin 6, ClauseSat (sample k q t) c)
    (x : B) (hx : fixed x k) : ClauseSat x c := by
  obtain ⟨t,et⟩:=escapeTable h k i j q hk ij
  obtain ⟨l,hl,ev⟩:=safe t
  refine ⟨l,hl,?_⟩
  by_cases p : l.1.1=0
  · have eq : l.1=(0,l.1.2) := Prod.ext p rfl
    rw [eq,show x (0,l.1.2)=(_==l.1.2) from hx _]
    rw [eq,show sample k q t (0,l.1.2)=(k==l.1.2) from sampleFixed k q t _] at ev
    exact ev
  · obtain e := (portShape ij cl hl).resolve_left p
    have eq : l.1=(l.1.1,h) := Prod.ext rfl e.1
    rw [eq,et _ p e.2.2.1 e.2.2.2,e.2.1] at ev
    contradiction

end PEqualNP.Outside.L_pcx_166.PairPorts

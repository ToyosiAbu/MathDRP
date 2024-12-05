import Mathlib.Order.SetNotation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.RingTheory.Ideal.Operations

namespace MvPolynomial
noncomputable section

variable {R : Type u} [CommRing R] [IsDomain R] [DecidableEq R] {σ : Type v} [DecidableEq (σ → R)]

-- For example, X i is the monomial x_i

example (i : σ) : MvPolynomial σ R := X i

-- A few definitions for the roots of a given MvPolynomial. TEMP : Ignoring Multiplicty for now, alternative definition for rootSet


-- def rootMultiplicity (a : σ → R) (p : MvPolynomial σ R) : ℕ :=
--   if ¬(MvPolynomial.eval a p) = (0: R) then
--     0
--   else 1 + rootMultiplicity a (p ∣ a)

-- theorem exists_multiset_roots {p : MvPolynomial σ R} (_ : p ≠ 0) : ∃ s : Multiset (σ → R),
--       (Multiset.card s : WithBot ℕ) ≤ totalDegree p ∧ ∀ a, s.count a = rootMultiplicity a p :=
--     sorry

-- def roots (p : MvPolynomial σ R) : Multiset (σ → R) :=
--   haveI := Classical.decEq R
--   haveI := Classical.dec (p = 0)
--   if h : p = 0 then ∅ else Classical.choose (exists_multiset_roots h)

-- def rootSet (p : MvPolynomial σ R) : Set (σ → R) := {x | x ∈ roots p}

def IsRoot (a: σ → R) (p : MvPolynomial σ R) : Prop := (MvPolynomial.eval a p) = (0: R)

def rootSet (p : MvPolynomial σ R) : Set (σ → R) := {x |  IsRoot x p}


-- Define projection of a set of tuples to a given coordinate d

def proj (s : Set (σ → R)) (d : σ) : Set R := {r | ∃ t : (σ → R), t ∈ s ∧ t d = r}

-- Define polynomial ring of a fixed variable as a subring of MvPolynomial σ R
-- f(x_d) is a single variable polynomial  .... addidative monomial in MvPolynomial algebra and prove using a singleton (subset of sigma) and prove we get a subalgebra

def univ_polynomial (R : Type u) [CommRing R] (d : σ) : Subsemiring (MvPolynomial σ R)
    where
  carrier := {p : MvPolynomial σ R | ∀ (v₁ v₂ : σ → R), (v₁ d = v₂ d) → (MvPolynomial.eval v₁ p = MvPolynomial.eval v₂ p)}
  zero_mem' := by
    intros v₁ v₂ h_eq
    simp [MvPolynomial.eval_zero]

  one_mem' := by
    intros v₁ v₂ h_eq
    simp [MvPolynomial.eval_C]

  add_mem' := by
    intros p q hp hq v₁ v₂ h
    simp [MvPolynomial.eval_add]
    rw [hp v₁ v₂ h, hq v₁ v₂ h]

  mul_mem' := by
    intros p q hp hq v₁ v₂ h
    simp [MvPolynomial.eval_mul]
    rw [hp v₁ v₂ h, hq v₁ v₂ h]


--  {p : MvPolynomial σ R | ∀ (v₁ v₂ : σ → R), (v₁ d = v₂ d) → (MvPolynomial.eval v₁ p = MvPolynomial.eval v₂ p)}
--     (v₁ d = v₂ d) → (MvPolynomial.eval v₁ p = MvPolynomial.eval v₂ p)}
-- { -- Define the carrier set of polynomials that only depend on d
--   have carrier := {p : MvPolynomial σ R | ∀ (v₁ v₂ : σ → R),
--     (v₁ d = v₂ d) → (MvPolynomial.eval v₁ p = MvPolynomial.eval v₂ p)}

--   have zero_mem' : ∀ (v₁ v₂ : σ → R), (v₁ d = v₂ d) →


--     have zero_eval : ∀ (v₁ v₂ : σ → R), (v₁ d = v₂ d) →
--       MvPolynomial.eval v₁ (0 : MvPolynomial σ R) = MvPolynomial.eval v₂ 0,
--     { intros v₁ v₂ h_eq,
--       simp [MvPolynomial.eval_zero] },
--     exact zero_eval
--   end

--   one_mem' :=
--   begin
--     have one_eval : ∀ (v₁ v₂ : σ → R), (v₁ d = v₂ d) →
--       MvPolynomial.eval v₁ (1 : MvPolynomial σ R) = MvPolynomial.eval v₂ 1,
--     { intros v₁ v₂ h_eq,
--       simp [MvPolynomial.eval_one] },
--     exact one_eval
--   end,

--   add_mem' :=
--   begin
--     have add_closed : ∀ p q ∈ carrier, ∀ (v₁ v₂ : σ → R), (v₁ d = v₂ d) →
--       MvPolynomial.eval v₁ (p + q) = MvPolynomial.eval v₂ (p + q),
--     { intros p q hp hq v₁ v₂ h_eq,
--       simp [MvPolynomial.eval_add],
--       rw [hp v₁ v₂ h_eq, hq v₁ v₂ h_eq] },
--     exact add_closed
--   end,
--   mul_mem' :=
--   begin
--     have mul_closed : ∀ p q ∈ carrier, ∀ (v₁ v₂ : σ → R), (v₁ d = v₂ d) →
--       MvPolynomial.eval v₁ (p * q) = MvPolynomial.eval v₂ (p * q),
--     { intros p q hp hq v₁ v₂ h_eq,
--       simp [MvPolynomial.eval_mul],
--       rw [hp v₁ v₂ h_eq, hq v₁ v₂ h_eq] },
--     exact mul_closed
--   end




--     -- Definition: zero polynomial is in the carrier
--   -- have zero_mem' :=
--   -- have zero_eval : (0 : MvPolynomial σ R) ∈ carrier := by
--   --   intros v₁ v₂ h_eq
--   --   simp [MvPolynomial.eval_zero]

--   -- have zero_mem' := by
--   --   have h : ∀ (v₁ v₂ : σ → R), v₁ d = v₂ d →
--   --     MvPolynomial.eval v₁ (0 : MvPolynomial σ R) = MvPolynomial.eval v₂ 0 := by
--   --       intros v₁ v₂ h_eq
--   --       simp [MvPolynomial.eval_zero]
--   --   exact h



--   -- -- Prove it contains 0
--   -- have zero_mem' := intros v₁ v₂ h
--   --   simp [MvPolynomial.eval_zero]
--   -- -- end,

--   -- -- Prove it contains 1
--   -- one_mem' :=
--   -- begin
--   --   intros v₁ v₂ h,
--   --   simp [MvPolynomial.eval_one],
--   -- end,

--   -- -- Prove it's closed under addition
--   -- add_mem' :=
--   -- begin
--   --   intros p q hp hq v₁ v₂ h,
--   --   simp [MvPolynomial.eval_add],
--   --   rw [hp v₁ v₂ h, hq v₁ v₂ h],
--   -- end,

--   -- -- Prove it's closed under multiplication
--   -- mul_mem' :=
--   -- begin
--   --   intros p q hp hq v₁ v₂ h,
--   --   simp [MvPolynomial.eval_mul],
--   --   rw [hp v₁ v₂ h, hq v₁ v₂ h],
--   -- end
-- }

-- The statement for Theorem 3
-- tau is the index for system of equations, we could also restrict it later if necessary to a finset of
-- ni pi thing si the common root, aka there is a solution for every indivisual

theorem elmination_polynomial {τ : Type w} (p : τ → MvPolynomial σ R) : Nat.card (⋂ i, (p i).rootSet) ≠ 0 → ∀ d : σ,
 ∃ f : univ_polynomial R d, (f : MvPolynomial σ R).totalDegree = Nat.card (proj (⋂ i, (p i).rootSet) d) ∧ proj (f : MvPolynomial σ R).rootSet d
 = proj (⋂ i, (p i).rootSet) d ∧ (f : MvPolynomial σ R) ∈ (Ideal.span {q | ∃ t : τ, q = p t}).radical := sorry


-- MvPolynomial.eval if we don't care about the multiplicity of roots, just that a root exists (Set of Roots vs MultiSet of Roots and their multiplicitu)

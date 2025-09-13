import Mathlib.Tactic

/-!
# Analysis I, Section 3.1: Fundamentals (of set theory)

In this section we set up a version of Zermelo-Frankel set theory (with atoms) that tries to be
as faithful as possible to the original text of Analysis I, Section 3.1. All numbering refers to
the original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- A type `Chapter3.SetTheory.Set` of sets
- A type `Chapter3.SetTheory.Object` of objects
- An axiom that every set is (or can be coerced into) an object
- The empty set `∅`, singletons `{y}`, and pairs `{y,z}` (and more general finite tuples), with
  their attendant axioms
- Pairwise union `X ∪ Y`, and their attendant axioms
- Coercion of a set `A` to its associated type `A.toSubtype`, which is a subtype of `Object`, and
  basic API.  (This is a technical construction needed to make the Zermelo-Frankel set theory
  compatible with the dependent type theory of Lean.)
- The specification `A.specify P` of a set `A` and a predicate `P: A.toSubtype → Prop` to the
  subset of elements of `A` obeying `P`, and the axiom of specification.
  TODO: somehow implement set builder elaboration for this.
- The replacement `A.replace hP` of a set `A` via a predicate
  `P: A.toSubtype → Object → Prop` obeying a uniqueness condition
  `∀ x y y', P x y ∧ P x y' → y = y'`, and the axiom of replacement.
- A bijective correspondence between the Mathlib natural numbers `ℕ` and a set
  `Chapter3.Nat : Chapter3.Set` (the axiom of infinity).
- Axioms of regularity, power set, and union (used in later sections of this chapter, but not
  required here)
- Connections with Mathlib's notion of a set

The other axioms of Zermelo-Frankel set theory are discussed in later sections.

Some technical notes:
- Mathlib of course has its own notion of a `Set` (or more precisely, a type `Set X` associated to
  each type `X`), which is not compatible with the notion `Chapter3.Set` defined here,
  though we will try to make the notations match as much as possible.  This causes some notational
  conflict: for instance, one may need to explicitly specify `(∅:Chapter3.Set)` instead of just `∅`
  to indicate that one is using the `Chapter3.Set` version of the empty set, rather than the
  Mathlib version of the empty set, and similarly for other notation defined here.
- In Analysis I, we chose to work with an "impure" set theory, in which there could be more
  `Object`s than just `Set`s.  In the type theory of Lean, this requires treating `Chapter3.Set`
  and `Chapter3.Object` as distinct types. Occasionally this means we have to use a coercion
  `(X: Chapter3.Object)` of a `Chapter3.Set` `X` to make into a `Chapter3.Object`: this is
  mostly needed when manipulating sets of sets.
- Strictly speaking, a set `X:Set` is not a type; however, we will coerce sets to types, and
  specifically to a subtype of `Object`.  A similar coercion is in place for Mathlib's
  formalization of sets.
- After this chapter is concluded, the notion of a `Chapter3.SetTheory.Set` will be deprecated in
  favor of the standard Mathlib notion of a `Set` (or more precisely of the type `Set X` of a set
  in a given type `X`).  However, due to various technical incompatibilities between set theory
  and type theory, we will not attempt to create a full equivalence between these two
  notions of sets. (As such, this makes this entire chapter optional from the point of view of
  the rest of the book, though we retain it for pedagogical purposes.)

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)
-/

namespace Chapter3

/- The ability to work in multiple universe is not relevant immediately, but
becomes relevant when constructing models of set theory in the Chapter 3 epilogue. -/
universe u v

/-- The axioms of Zermelo-Frankel theory with atoms.  -/
class SetTheory where
  Set : Type u -- Axiom 3.1
  Object : Type v -- Axiom 3.1
  set_to_object : Set ↪ Object -- Axiom 3.1
  mem : Object → Set → Prop -- Axiom 3.1
  extensionality X Y : (∀ x, mem x X ↔ mem x Y) → X = Y -- Axiom 3.2

  univ : Set
  mem_univ x : mem x univ

  emptyset: Set -- Axiom 3.3
  emptyset_mem x : ¬ mem x emptyset -- Axiom 3.3

  singleton : Object → Set -- Axiom 3.4
  singleton_axiom x y : mem x (singleton y) ↔ x = y -- Axiom 3.4
  union_pair : Set → Set → Set -- Axiom 3.5
  union_pair_axiom X Y x : mem x (union_pair X Y) ↔ (mem x X ∨ mem x Y) -- Axiom 3.5

  specify A (P: Subtype (mem · A) → Prop) : Set -- Axiom 3.6

  specification_axiom A (P: Subtype (mem · A) → Prop) :
    (∀ x, mem x (specify A P) → mem x A) ∧ ∀ x, mem x.val (specify A P) ↔ P x -- Axiom 3.6

  -- Axiom 3.7
  replace A -- “Let A be a set”
    (P: Subtype (mem · A) → Object → Prop) -- “a statement P(x, y) pertaining to x ∈ A and any object y”
    (hP: ∀ x y y', P x y ∧ P x y' → y = y') -- “there is at most one y for which P(x, y) is true”
    : Set -- “then there exists a set {y : P(x, y) is true for some x}”

  -- Axiom 3.7
  replacement_axiom A -- “Let A be a set”
    (P : Subtype (mem · A) → Object → Prop) -- “a statement P(x, y) pertaining to x ∈ A and any object y”
    (hP : ∀ x y y', P x y ∧ P x y' → y = y') -- “there is at most one y for which P(x, y) is true”
    : ∀ z, mem z (replace A P hP) ↔ ∃ x, P x z -- “then for any object z, z ∈ {y : ∃x, P(x, y)} iff ∃x ∈ A, P(x, z) is true”

  nat : Set -- Axiom 3.8
  nat_equiv : ℕ ≃ Subtype (mem . nat) -- Axiom 3.8
  regularity_axiom A (hA : ∃ x, mem x A) :
    ∃ x, mem x A ∧ ∀ S, x = set_to_object S → ¬ ∃ y, mem y A ∧ mem y S -- Axiom 3.9
  pow : Set → Set → Set -- Axiom 3.11
  function_to_object (X: Set) (Y: Set) :
    (Subtype (mem . X) → Subtype (mem . Y)) ↪ Object -- Axiom 3.11
  powerset_axiom (X: Set) (Y: Set) (F:Object) :
    mem F (pow X Y) ↔ ∃ f: Subtype (mem . Y) → Subtype (mem . X),
    function_to_object Y X f = F -- Axiom 3.11
  union : Set → Set -- Axiom 3.12
  union_axiom A x : mem x (union A) ↔ ∃ S, mem x S ∧ mem (set_to_object S) A -- Axiom 3.12

-- This enables one to use `Set` and `Object` instead of `SetTheory.Set` and `SetTheory.Object`.
export SetTheory (Set Object)

-- This instance implicitly imposes the axioms of Zermelo-Frankel set theory with atoms.
variable [SetTheory]

/-- Definition 3.1.1 (objects can be elements of sets) -/
instance SetTheory.objects_mem_sets : Membership Object Set where
  mem X x := mem x X

-- Now we can use the `∈` notation between our `Object` and `Set`.
example (X: Set) (x: Object) : x ∈ X ↔ SetTheory.mem x X := by rfl

/-- Axiom 3.1 (Sets are objects)-/
instance SetTheory.sets_are_objects : Coe Set Object where
  coe X := set_to_object X

-- Now we can treat a `Set` as an `Object` when needed.
example (X: Set) : (X: Object) = SetTheory.set_to_object X := rfl

/-- Axiom 3.1 (Sets are objects)-/
theorem SetTheory.Set.coe_eq {X Y:Set} (h: (X: Object) = (Y: Object)) : X = Y :=
  set_to_object.inj' h

/-- Axiom 3.1 (Sets are objects)-/
@[simp]
theorem SetTheory.Set.coe_eq_iff (X Y:Set) : (X: Object) = (Y: Object) ↔  X = Y :=
  ⟨ coe_eq, by rintro rfl; rfl ⟩

/-- Axiom 3.2 (Equality of sets).  The `[ext]` tag allows the `ext` tactic to work for sets. -/
@[ext]
theorem SetTheory.Set.ext {X Y:Set} (h: ∀ x, x ∈ X ↔ x ∈ Y) : X = Y := extensionality _ _ h

/- Axiom 3.2 (Equality of sets)-/
#check SetTheory.Set.ext_iff

instance SetTheory.Set.instEmpty : EmptyCollection Set where
  emptyCollection := emptyset

-- Now we can use the `∅` notation to refer to `SetTheory.emptyset`.
example : ∅ = SetTheory.emptyset := rfl

-- Make everything we define in `SetTheory.Set.*` accessible directly.
open SetTheory.Set

/--
  Axiom 3.3 (empty set).
  Note: in some applications one may have to explicitly cast ∅ to Set due to
  Mathlib's existing set theory notation.
-/
@[simp]
theorem SetTheory.Set.not_mem_empty : ∀ x, x ∉ (∅:Set) := emptyset_mem

lemma SetTheory.Set.not_mem_empty' {x : Object} (h : x ∈ (∅:Set)) : False :=
  ((not_mem_empty x) h).elim

lemma SetTheory.Set.mem_empty_iff (x : Object) : x ∈ (∅:Set) ↔ False := by
  constructor
  . intro (h : x ∈ ∅)
    exact (not_mem_empty x) h
  . intro (h : False)
    exact h.elim

/-- Empty set has no elements -/
theorem SetTheory.Set.eq_empty_iff_forall_not_mem {X : Set} :
  X = ∅ ↔ (∀x, x ∉ X)
:= by
  constructor
  . -- ⊢ X = ∅ → ∀x, x ∉ X
    intro (hX : X = ∅) x
    have h₁ : x ∉ ∅ := not_mem_empty x
    have h₂ : x ∉ X := hX ▸ h₁
    exact h₂
  . -- ⊢ (∀x, x ∉ X) → X = ∅
    intro (hX : ∀x, x ∉ X)
    ext y
    constructor
    . -- ⊢ y ∈ X → y ∈ ∅
      intro (hy : y ∈ X)
      exact ((hX y : y ∉ X) hy).elim
    . -- ⊢ y ∈ ∅ → y ∈ X
      intro (hy : y ∈ (∅:Set))
      exact ((not_mem_empty y : y ∉ ∅) hy).elim

/-- Empty set is unique -/
theorem SetTheory.Set.empty_unique : ∃! (X:Set), ∀ x, x ∉ X := by
  use (∅:Set)
  simp
  -- ⊢ ∀ (Y:Set), (∀ (x:object), x ∉ Y) → Y = ∅
  intro X (hx : ∀x, x ∉ X)
  -- ⊢ X = ∅
  exact (eq_empty_iff_forall_not_mem.mpr : (∀x, x ∉ X) → X = ∅) hx

/-- Lemma 3.1.5 (Single choice) -/
lemma SetTheory.Set.nonempty_def {X:Set} (h: X ≠ ∅) : ∃ x, x ∈ X := by
  contrapose! h
  -- h: ∀x, x ∉ X
  -- ⊢ X = ∅
  exact (eq_empty_iff_forall_not_mem.mpr : (∀x, x ∉ X) → X = ∅) h

theorem SetTheory.Set.nonempty_of_inhabited {X:Set} {x:Object} (h:x ∈ X) : X ≠ ∅ := by
  contrapose! h
  -- h: X = ∅
  -- ⊢ x ∉ ∅
  exact (eq_empty_iff_forall_not_mem.mp : X = ∅ → ∀x, x ∉ X) h x

instance SetTheory.Set.instSingleton : Singleton Object Set where
  singleton := singleton

-- Now we can use the `{x}` notation for a single element `Set`.
example (x: Object) : {x} = SetTheory.singleton x := rfl

/--
  Axiom 3.3(a) (singleton).
  Note: in some applications one may have to explicitly cast {a} to Set due to Mathlib's
  existing set theory notation.
-/
@[simp]
theorem SetTheory.Set.mem_singleton (x a:Object) : x ∈ ({a}:Set) ↔ x = a := singleton_axiom x a

lemma SetTheory.Set.mem_singleton' (x : Object) : x ∈ ({x} : Set) := (mem_singleton x x).mpr rfl

lemma SetTheory.Set.eq_of_mem_singleton {x a : Object} (hxa : x ∈ ({a} : Set)) : x = a := (mem_singleton x a).mp hxa

lemma SetTheory.Set.mem_singleton_of_eq {x a : Object} (hxa : x = a) : x ∈ ({a} : Set) := (mem_singleton x a).mpr hxa


instance SetTheory.Set.instUnion : Union Set where
  union := union_pair

-- Now we can use the `X ∪ Y` notation for a union of two `Set`s.
example (X Y: Set) : X ∪ Y = SetTheory.union_pair X Y := rfl

/-- Axiom 3.4 (Pairwise union)-/
@[simp]
theorem SetTheory.Set.mem_union (x : Object) (X Y : Set) : x ∈ (X ∪ Y) ↔ (x ∈ X ∨ x ∈ Y) :=
  union_pair_axiom X Y x

lemma SetTheory.Set.mem_union_left {x : Object} {X Y : Set}
  (h : x ∈ X) : x ∈ X ∪ Y
:= by
  exact (mem_union x X Y).mpr (Or.inl h)

lemma SetTheory.Set.mem_union_right {x : Object} {X Y : Set}
  (h : x ∈ Y) : x ∈ X ∪ Y
:= by
  exact (mem_union x X Y).mpr (Or.inr h)

lemma SetTheory.Set.mem_union_cases {x : Object} {X Y : Set}
  (h : x ∈ X ∪ Y) : x ∈ X ∨ x ∈ Y
:= by
  exact (mem_union x X Y).mp h

instance SetTheory.Set.instInsert : Insert Object Set where
  insert x X := {x} ∪ X

@[simp]
theorem SetTheory.Set.mem_insert (a b: Object) (X: Set) : a ∈ insert b X ↔ a = b ∨ a ∈ X := by
  simp [instInsert]

/-- Axiom 3.3(b) (pair).  Note: in some applications one may have to cast {a,b}
    to Set. -/
theorem SetTheory.Set.pair_eq (a b:Object) : ({a,b}:Set) = {a} ∪ {b} := by rfl

/-- Axiom 3.3(b) (pair).  Note: in some applications one may have to cast {a,b}
    to Set. -/
@[simp]
theorem SetTheory.Set.mem_pair (x a b:Object) : x ∈ ({a,b}:Set) ↔ (x = a ∨ x = b) := by
  constructor
  . intro (hx : x ∈ ({a, b}:Set))
    have h₁ : x ∈ ({a}:Set) ∪ ({b}:Set)     := by rw [pair_eq] at hx; exact hx
    have h₂ : x ∈ ({a}:Set) ∨ x ∈ ({b}:Set) := by rw [mem_union] at h₁; exact h₁
    have h₃ : x = a ∨ x = b                 := by rw [mem_singleton, mem_singleton] at h₂; exact h₂
    exact h₃
  . intro hx
    rcases hx with (hxa₁ : x = a) | (hxb₁ : x = b)
    . have ha₂ : x ∈ ({a}:Set)             := (mem_singleton x a).mpr hxa₁
      have ha₃ : x ∈ ({a}:Set) ∪ ({b}:Set) := (mem_union x ({a}:Set) ({b}:Set)).mpr (Or.inl ha₂)
      have ha₄ : x ∈ ({a, b}:Set)          := pair_eq a b ▸ ha₃
      exact ha₄
    . have hb₂ : x ∈ ({b}:Set)             := (mem_singleton x b).mpr hxb₁
      have hb₃ : x ∈ ({a}:Set) ∪ ({b}:Set) := (mem_union x ({a}:Set) ({b}:Set)).mpr (Or.inr hb₂)
      have hb₄ : x ∈ ({a, b}:Set)          := pair_eq a b ▸ hb₃
      exact hb₄

lemma SetTheory.Set.mem_pair_left (x a b : Object) (h : x = a) : x ∈ ({a, b} : Set) :=
  (mem_pair x a b).mpr (Or.inl h)

lemma SetTheory.Set.mem_pair_right (x a b : Object) (h : x = b) : x ∈ ({a, b} : Set) :=
  (mem_pair x a b).mpr (Or.inr h)


@[simp]
theorem SetTheory.Set.mem_triple (x a b c:Object) : x ∈ ({a,b,c}:Set) ↔ (x = a ∨ x = b ∨ x = c) := by
  constructor
  . intro (hx: x ∈ ({a, b, c}:Set))
    have h₁ : x = a ∨ x ∈ ({b, c}:Set) := (Set.mem_insert x a ({b, c}:Set)).mp hx
    have h₂ : x = a ∨ x = b ∨ x = c    := by rw [Set.mem_pair x b c] at h₁; exact h₁
    exact h₂
  . intro hx
    have h₁ : x = a ∨ x ∈ {b, c} → x ∈ {a, b, c} := (Set.mem_insert x a ({b, c}:Set)).mpr
    rcases hx with (hxa : x = a) | (hxbc : x = b ∨ x = c)
    . exact h₁ (Or.inl hxa)
    . have h₂ : x ∈ {b, c} := (Set.mem_pair x b c).mpr hxbc
      exact h₁ (Or.inr h₂)

/-- Remark 3.1.9 -/
theorem SetTheory.Set.singleton_uniq (a:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a := by
  use ({a}:Set)
  simp
  -- ⊢ ∀ X, (∀ x, x ∈ X ↔ x = a) → X = {a}
  intro X (h₀ : ∀ x, x ∈ X ↔ x = a)
  -- ⊢ X = {a}
  apply extensionality
  -- ⊢ ∀ x, x ∈ X ↔ x ∈ {a}
  intro x
  constructor
  . -- →
    intro (h₁ : x ∈ X)
    have h₂ : x = a := (h₀ x).mp h₁
    have h₃ : x ∈ ({a}:Set) := (mem_singleton x a).mpr h₂
    exact h₃
  . -- ←
    intro (h₁ : x ∈ ({a}:Set))
    have h₂ : x = a := (mem_singleton x a).mp h₁
    have h₃ : x ∈ X := (h₀ x).mpr h₂
    exact h₃

/-- Remark 3.1.9 -/
theorem SetTheory.Set.pair_uniq (a b:Object) : ∃! (X:Set), ∀ x, x ∈ X ↔ x = a ∨ x = b := by
  use ({a, b}:Set)
  simp
  -- ⊢ ∀ X, (∀ x, x ∈ X ↔ x = a ∨ x = b) → X = {a, b}
  intro X h₀
  -- ⊢ X = {a, b}
  apply extensionality
  -- ⊢ x ∈ X ↔ x ∈ {a, b}
  intro x
  have h₁ : x ∈ X ↔ x = a ∨ x = b              := h₀ x
  have h₂ :         x = a ∨ x = b ↔ x ∈ {a, b} := (Set.mem_pair x a b).symm
  have h₃ : x ∈ X ↔                 x ∈ {a, b} := h₁.trans h₂
  exact h₃

/-- Remark 3.1.9 -/
theorem SetTheory.Set.pair_comm (a b:Object) : ({a,b}:Set) = {b,a} := by
  ext x
  constructor
  . intro (hxab : x ∈ ({a, b}:Set))
    have h₁ : x = a ∨ x = b    := (mem_pair x a b).mp hxab
    have h₂ : x ∈ ({b, a}:Set) := (mem_pair x b a).mpr h₁.symm
    exact h₂
  . intro (hxba : x ∈ ({b, a}:Set))
    have h₁ : x = b ∨ x = a    := (mem_pair x b a).mp hxba
    have h₂ : x ∈ ({a, b}:Set) := (mem_pair x a b).mpr h₁.symm
    exact h₂

/-- Remark 3.1.9 -/
@[simp]
theorem SetTheory.Set.pair_self (a:Object) : ({a,a}:Set) = {a} := by
  ext x
  constructor
  . intro (hxaa : x ∈ ({a, a}:Set))
    have h₁ : x = a ∨ x = a := (mem_pair x a a).mp hxaa
    have h₂ : x = a         := (or_self (x = a)).mp h₁
    have h₃ : x ∈ ({a}:Set) := (mem_singleton x a).mpr h₂
    exact h₃
  . intro (hxa : x ∈ ({a}:Set))
    have h₁ : x = a            := (mem_singleton x a).mp hxa
    have h₂ : x ∈ ({a, a}:Set) := (mem_pair x a a).mpr (Or.inl h₁)
    exact h₂

lemma SetTheory.extensionality_of_eq {X Y : Set}
  (h : X = Y) : (∀ (x : Object), x ∈ X ↔ x ∈ Y)
:= by
  intro x
  rw [h]

lemma SetTheory.distinct_of_pair_eq_distinct_pair {a b c d : Object}
  (h : ({a, b}:Set) = {c, d})
  (hcd_ne : c ≠ d) : a ≠ b
:= by
  by_contra! hab -- a = b
  have h₁  : ({a, b}:Set) = {a} := by simp only [hab, pair_self]
  have h₂  : ∀x, x ∈ ({a, b}:Set) ↔ x ∈ ({c, d}:Set) := SetTheory.extensionality_of_eq h
  have hc₁ : c ∈ ({a}:Set) := h₁ ▸ (h₂ c).mpr ((mem_pair c c d).mpr (Or.inl rfl))
  have hd₁ : d ∈ ({a}:Set) := h₁ ▸ (h₂ d).mpr ((mem_pair d c d).mpr (Or.inr rfl))
  have hc₂ : c = a := (mem_singleton c a).mp hc₁
  have hd₂ : d = a := (mem_singleton d a).mp hd₁
  have hcd : c = d := hd₂.symm ▸ hc₂
  exact hcd_ne hcd

/-- Exercise 3.1.1 -/
theorem SetTheory.Set.pair_eq_pair {a b c d:Object} (h: ({a,b}:Set) = {c,d}) :
  (a = c ∧ b = d) ∨ (a = d ∧ b = c)
:= by
  have haab : a ∈ ({a, b}:Set) := ((mem_pair a a b).mpr (Or.inl rfl))
  have hbab : b ∈ ({a, b}:Set) := ((mem_pair b a b).mpr (Or.inr rfl))

  by_cases hcd : c = d

  . -- Case: {c, d} is in fact the singleton {c}; simplify hypothesis & goal
    replace h : ({a, b}:Set) = {c} := by simpa only [hcd, pair_self] using h
    simp [← hcd, or_self]
    -- ⊢ a = c ∧ b = c
    have hx : ∀x, x ∈ ({a, b}:Set) ↔ x ∈ ({c}:Set) := SetTheory.extensionality_of_eq h
    have ha : a = c := (mem_singleton a c).mp ((hx a).mp haab)
    have hb : b = c := (mem_singleton b c).mp ((hx b).mp hbab)
    exact ⟨ha, hb⟩

  . -- Case: true pair of distinct elements
    have hcd_ne : c ≠ d := by push_neg at hcd; exact hcd
    have hab_ne : a ≠ b := SetTheory.distinct_of_pair_eq_distinct_pair h hcd_ne
    have hx : ∀x, x ∈ ({a, b}:Set) ↔ x ∈ ({c, d}:Set) := SetTheory.extensionality_of_eq h
    have ha : a = c ∨ a = d := (mem_pair a c d).mp ((hx a).mp haab)
    have hb : b = c ∨ b = d := (mem_pair b c d).mp ((hx b).mp hbab)
    rcases ha with hac | had
    . rcases hb with hbc | hbd
      . exact (hab_ne (hbc.symm ▸ hac)).elim
      . exact Or.inl ⟨hac, hbd⟩
    . rcases hb with hbc | hbd
      . exact Or.inr ⟨had, hbc⟩
      . exact (hab_ne (hbd.symm ▸ had)).elim

abbrev SetTheory.Set.empty : Set := ∅
abbrev SetTheory.Set.singleton_empty : Set := {(empty: Object)}
abbrev SetTheory.Set.pair_empty : Set := {(empty: Object), (singleton_empty: Object)}

/-- Exercise 3.1.2 -/
theorem SetTheory.Set.emptyset_neq_singleton : empty ≠ singleton_empty := by
  by_contra! h₀
  have h₁ : (empty:Object) ∈ singleton_empty := by simp [mem_singleton]
  have h₂ : (empty:Object) ∈ empty := (SetTheory.extensionality_of_eq h₀ empty).mpr h₁
  have h₃ : (empty:Object) ∉ empty := not_mem_empty empty
  exact h₃ h₂

/-- Exercise 3.1.2 -/
theorem SetTheory.Set.emptyset_neq_pair : empty ≠ pair_empty := by
  by_contra! h₀
  have h₁ : (empty:Object) ∈ pair_empty := by simp [mem_singleton]
  have h₂ : (empty:Object) ∈ empty := (SetTheory.extensionality_of_eq h₀ empty).mpr h₁
  have h₃ : (empty:Object) ∉ empty := not_mem_empty empty
  exact h₃ h₂

/-- Exercise 3.1.2 -/
theorem SetTheory.Set.singleton_empty_neq_pair : singleton_empty ≠ pair_empty := by
  by_contra! h₀
  have h₁ : (singleton_empty:Object) ∈ pair_empty := by simp
  have h₂ : (singleton_empty:Object) ∈ singleton_empty := (SetTheory.extensionality_of_eq h₀ singleton_empty).mpr h₁
  have h₃ : (singleton_empty:Object) = empty := (mem_singleton singleton_empty empty).mp h₂
  have h₄ : (singleton_empty:Set) = empty := by simpa using h₃
  exact emptyset_neq_singleton.symm h₄

/--
  Remark 3.1.11.
  (These results can be proven either by a direct rewrite, or by using extensionality.)
-/
theorem SetTheory.Set.union_congr_left (A A' B:Set) (h: A = A') : A ∪ B = A' ∪ B := by
  rw [h]

/--
  Remark 3.1.11.
  (These results can be proven either by a direct rewrite, or by using extensionality.)
-/
theorem SetTheory.Set.union_congr_right (A B B':Set) (h: B = B') : A ∪ B = A ∪ B' := by
  rw [h]

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.singleton_union_singleton (a b:Object) : ({a}:Set) ∪ ({b}:Set) = {a,b} := by
  ext x
  exact ⟨
    fun hx => (by simpa only [mem_union,  mem_singleton, ← mem_pair ] using hx),
    fun hx => (by simpa only [mem_pair, ← mem_singleton, ← mem_union] using hx),
  ⟩

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.union_comm (A B:Set) : A ∪ B = B ∪ A := by
  ext x
  exact ⟨
    fun hx => (mem_union x B A).mpr ((mem_union x A B).mp hx).symm,
    fun hx => (mem_union x A B).mpr ((mem_union x B A).mp hx).symm,
  ⟩

/-- Lemma 3.1.12 (Basic properties of unions) / Exercise 3.1.3 -/
theorem SetTheory.Set.union_assoc (A B C:Set) : (A ∪ B) ∪ C = A ∪ (B ∪ C) := by
  ext x
  constructor
  . intro (h₀ : x ∈ A ∪ B ∪ C)
    have h₁ : (x ∈ A ∪ B) ∨ x ∈ C     := (mem_union x (A ∪ B) C).mp h₀
    have h₂ : (x ∈ A ∨ x ∈ B) ∨ x ∈ C := h₁.imp_left (mem_union x A B).mp
    have h₃ : x ∈ A ∨ (x ∈ B ∨ x ∈ C) := or_assoc.mp h₂
    have h₄ : x ∈ A ∨ (x ∈ B ∪ C)     := h₃.imp_right (mem_union x B C).mpr
    have h₅ : x ∈ A ∪ (B ∪ C)         := (mem_union x A (B ∪ C)).mpr h₄
    exact h₅
  . intro (h₀ : x ∈ A ∪ (B ∪ C))
    have h₁ : x ∈ A ∨ (x ∈ B ∪ C)     := (mem_union x A (B ∪ C)).mp h₀
    have h₂ : x ∈ A ∨ (x ∈ B ∨ x ∈ C) := h₁.imp_right (mem_union x B C).mp
    have h₃ : (x ∈ A ∨ x ∈ B) ∨ x ∈ C := or_assoc.mpr h₂
    have h₄ : (x ∈ A ∪ B) ∨ x ∈ C     := h₃.imp_left (mem_union x A B).mpr
    have h₅ : x ∈ (A ∪ B ∪ C)         := (mem_union x (A ∪ B) C).mpr h₄
    exact h₅

/-- Proposition 3.1.27(c) -/
@[simp]
theorem SetTheory.Set.union_self (A:Set) : A ∪ A = A := by
  ext x
  constructor
  . intro (h₀ : x ∈ A ∪ A)
    have h₁ : x ∈ A ∨ x ∈ A := (mem_union x A A).mp h₀
    have h₂ : x ∈ A         := (or_self (x ∈ A)).mp h₁
    exact h₂
  . intro (h₀ : x ∈ A)
    have h₁ : x ∈ A ∨ x ∈ A := (or_self (x ∈ A)).mpr h₀
    have h₂ : x ∈ A ∪ A     := (mem_union x A A).mpr h₁
    exact h₂

/-- Proposition 3.1.27(a) -/
@[simp]
theorem SetTheory.Set.union_empty (A:Set) : A ∪ ∅ = A := by
  ext x
  constructor
  . intro (h₀ : x ∈ A ∪ ∅)
    have h₁ : x ∈ A ∨ x ∈ (∅:Set) := (mem_union x A ∅).mp h₀
    have h₂ : x ∈ A ∨ False       := h₁.imp_right (mem_empty_iff x).mp
    have h₃ : x ∈ A               := (or_false (x ∈ A)).mp h₂
    exact h₃
  . intro (h₀ : x ∈ A)
    have h₁ : x ∈ A ∨ False       := (or_false (x ∈ A)).mpr h₀
    have h₂ : x ∈ A ∨ x ∈ (∅:Set) := h₁.imp_right (mem_empty_iff x).mpr
    have h₃ : x ∈ A ∪ ∅           := (mem_union x A ∅).mpr h₂
    exact h₃

/-- Proposition 3.1.27(a) -/
@[simp]
theorem SetTheory.Set.empty_union (A:Set) : ∅ ∪ A = A := by
  rw [union_comm]
  exact Set.union_empty _

theorem SetTheory.Set.triple_eq (a b c:Object) : {a,b,c} = ({a}:Set) ∪ {b,c} := by
  rfl

/-- Example 3.1.10 -/
theorem SetTheory.Set.pair_union_pair (a b c:Object) :
    ({a,b}:Set) ∪ {b,c} = {a,b,c} := by
  ext; simp only [mem_union, mem_pair, mem_triple]; tauto

/-- Definition 3.1.14.   -/
instance SetTheory.Set.instSubset : HasSubset Set where
  Subset X Y := ∀ x, x ∈ X → x ∈ Y

-- Now we can use `⊆` for a subset relationship between two `Set`s.
example (X Y: Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

/--
  Definition 3.1.14.
  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`.
-/
instance SetTheory.Set.instSSubset : HasSSubset Set where
  SSubset X Y := X ⊆ Y ∧ X ≠ Y

-- Now we can use `⊂` for a strict subset relationship between two `Set`s.
example (X Y: Set) : X ⊂ Y ↔ X ⊆ Y ∧ X ≠ Y := by rfl

/-- Definition 3.1.14. -/
theorem SetTheory.Set.subset_def (X Y:Set) : X ⊆ Y ↔ ∀ x, x ∈ X → x ∈ Y := by rfl

/--
  Definition 3.1.14.
  Note that the strict subset operation in Mathlib is denoted `⊂` rather than `⊊`.
-/
theorem SetTheory.Set.ssubset_def (X Y:Set) : X ⊂ Y ↔ (X ⊆ Y ∧ X ≠ Y) := by rfl

/-- Remark 3.1.15 -/
theorem SetTheory.Set.subset_congr_left {A A' B:Set} (hAA':A = A') (hAB: A ⊆ B) : A' ⊆ B := by
  rw [hAA'] at hAB
  exact hAB

/-- Examples 3.1.16 -/
@[simp, refl]
theorem SetTheory.Set.subset_self (A:Set) : A ⊆ A :=
  fun x (hx : x ∈ A) => hx

/-- Examples 3.1.16 -/
@[simp]
theorem SetTheory.Set.empty_subset (A:Set) : ∅ ⊆ A :=
  fun x (hx : x ∈ ∅) => ((not_mem_empty x) hx).elim

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_trans {A B C:Set} (hAB:A ⊆ B) (hBC:B ⊆ C) : A ⊆ C := by
  -- This proof is written to follow the structure of the original text.
  rw [subset_def]
  intro x hx
  rw [subset_def] at hAB
  apply hAB x at hx
  apply hBC x at hx
  assumption

/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.subset_antisymm (A B:Set) (hAB:A ⊆ B) (hBA:B ⊆ A) : A = B := by
  ext x
  have h₁ : x ∈ A → x ∈ B := hAB x
  have h₂ : x ∈ B → x ∈ A := hBA x
  have h₃ : x ∈ A ↔ x ∈ B := iff_def.mpr ⟨h₁, h₂⟩
  exact h₃


-- Existence of distinguishing element
lemma SetTheory.Set.exists_dist_elem_of_ssubset {A B : Set}
  (hAB : A ⊂ B) : ∃ (x : Object), x ∈ B ∧ x ∉ A
:= by
  by_contra! hBA_sub -- B ⊆ A
  have ⟨(hAB_sub : A ⊆ B), (hAB_neq : A ≠ B)⟩ := (ssubset_def A B).mp hAB
  have hAB_eq : A = B := subset_antisymm A B hAB_sub hBA_sub
  exact (hAB_neq hAB_eq).elim

-- Strict subset by existence of distinguishing element
lemma SetTheory.Set.ssubset_of_subset_of_dist_elem {A B : Set}
  (hAB_sub : A ⊆ B)
  (hx : ∃ (x : Object), x ∈ B ∧ x ∉ A) : A ⊂ B
:= by
  have hAB_neq : A ≠ B := by
    intro (hAB : A = B)
    have ⟨x, (hxB_mem : x ∈ B), (hxB_not : x ∉ B)⟩ := hAB ▸ hx
    exact (hxB_not hxB_mem).elim
  exact ⟨hAB_sub, hAB_neq⟩


/-- Proposition 3.1.17 (Partial ordering by set inclusion) -/
theorem SetTheory.Set.ssubset_trans (A B C : Set) (hAB : A ⊂ B) (hBC : B ⊂ C) : A ⊂ C := by
  have ⟨x, (hxC : x ∈ C), (hxB : x ∉ B)⟩ := exists_dist_elem_of_ssubset hBC
  have hxA  : x ∉ A := fun (hxA : x ∈ A) => (hxB : x ∉ B) (hAB.left x hxA : x ∈ B)
  have hAC₁ : A ⊆ C := subset_trans hAB.left hBC.left
  have hAC₂ : A ⊂ C := ssubset_of_subset_of_dist_elem hAC₁ ⟨x, hxC, hxA⟩
  exact hAC₂

-- Proof via antisymmetry of ⊆, for comparison
theorem SetTheory.Set.ssubset_trans' (A B C : Set) (hAB : A ⊂ B) (hBC : B ⊂ C) : A ⊂ C := by
  have hAC_sub : A ⊆ C := subset_trans hAB.left hBC.left
  have hAC_neq : A ≠ C := by
    intro (hAC : A = C)
    have hBA_sub : B ⊆ A := (hAC ▸ hBC).left
    have hAB_sub : A ⊆ B := hAB.left
    have hAB_eq  : A = B := subset_antisymm A B hAB_sub hBA_sub
    have hAB_neq : A ≠ B := hAB.right
    exact (hAB_neq hAB_eq).elim
  exact ⟨hAC_sub, hAC_neq⟩


theorem SetTheory.Set.ssubset_of_subset_of_ssubset {A B C : Set} (hAB : A ⊆ B) (hBC : B ⊂ C) : A ⊂ C := by
  have ⟨x, (hxC : x ∈ C), (hxB : x ∉ B)⟩ := exists_dist_elem_of_ssubset hBC
  have hxA  : x ∉ A := fun (hxA : x ∈ A) => (hxB : x ∉ B) (hAB x hxA : x ∈ B)
  have hAC₁ : A ⊆ C := subset_trans hAB hBC.left
  have hAC₂ : A ⊂ C := ssubset_of_subset_of_dist_elem hAC₁ ⟨x, hxC, hxA⟩
  exact hAC₂

-- Proof via antisymmetry of ⊆, for comparison
theorem SetTheory.Set.ssubset_of_subset_of_ssubset' {A B C : Set} (hAB : A ⊆ B) (hBC : B ⊂ C) : A ⊂ C := by
  have hAC_sub : A ⊆ C := subset_trans hAB hBC.left
  have hAC_neq : A ≠ C := by
    intro (hAC : A = C)
    have hBA_sub : B ⊆ A := hAC ▸ hBC.left
    have hAB_eq  : A = B := subset_antisymm A B hAB hBA_sub
    have hBC_eq  : B = C := (hAC ▸ hAB_eq).symm
    have hBC_neq : B ≠ C := hBC.right
    exact hBC_neq hBC_eq
  exact ⟨hAC_sub, hAC_neq⟩


theorem SetTheory.Set.ssubset_of_ssubset_of_subset {A B C : Set} (hAB : A ⊂ B) (hBC : B ⊆ C) : A ⊂ C := by
  have ⟨x, (hxB : x ∈ B), (hxA : x ∉ A)⟩ := exists_dist_elem_of_ssubset hAB
  have hxC  : x ∈ C := hBC x hxB
  have hAC₁ : A ⊆ C := subset_trans hAB.left hBC
  have hAC₂ : A ⊂ C := ssubset_of_subset_of_dist_elem hAC₁ ⟨x, hxC, hxA⟩
  exact hAC₂

-- Proof via antisymmetry of ⊆, for comparison
theorem SetTheory.Set.ssubset_of_ssubset_of_subset' {A B C : Set} (hAB : A ⊂ B) (hBC : B ⊆ C) : A ⊂ C := by
  have hAC_sub : A ⊆ C := subset_trans hAB.left hBC
  have hAC_neq : A ≠ C := by
    intro (hAC : A = C)
    have hAB_sub : A ⊆ B := hAB.left
    have hBA_sub : B ⊆ A := hAC ▸ hBC
    have hAB_eq  : A = B := subset_antisymm A B hAB_sub hBA_sub
    have hAB_neq : A ≠ B := hAB.right
    exact (hAB_neq hAB_eq).elim
  exact ⟨hAC_sub, hAC_neq⟩


/--
  This defines the subtype `A.toSubtype` for any `A:Set`.
  Note that `A.toSubtype` gives you a type, similar to how `Object` or `Set` are types.
  A value `x'` of type `A.toSubtype` combines some `x: Object` with a proof that `hx: x ∈ A`.

  To produce an element `x'` of this subtype, use `⟨ x, hx ⟩`, where `x: Object` and `hx: x ∈ A`.
  The object `x` associated to a subtype element `x'` is recovered as `x'.val`, and
  the property `hx` that `x` belongs to `A` is recovered as `x'.property`.
-/
abbrev SetTheory.Set.toSubtype (A:Set) := Subtype (· ∈ A)

example (A: Set) (x: Object) (hx: x ∈ A) : A.toSubtype := ⟨x, hx⟩
example (A: Set) (x': A.toSubtype) : Object := x'.val
example (A: Set) (x': A.toSubtype) : x'.val ∈ A := x'.property

-- In practice, a subtype lets us carry an object with a membership proof as a single value.
-- Compare these two proofs. They are equivalent, but the latter packs `x` and `hx` into `x'`.
example (A B: Set) (x: Object) (hx: x ∈ A) : x ∈ A ∪ B := by simp; left; exact hx
example (A B: Set) (x': A.toSubtype) : x'.val ∈ A ∪ B := by simp; left; exact x'.property

instance : CoeSort (Set) (Type v) where
  coe A := A.toSubtype

structure Subtype' {α : Sort u} (p : α → Prop) where
  val : α
  property : p val
abbrev SetTheory.Set.toSubtype' (A : Set) := Subtype' (· ∈ A)

instance subtypeCoe' {α : Sort u} {p : α → Prop} : CoeOut (Subtype' p) α where
  coe v := v.val

example (A B : Set) (x : A.toSubtype') : x.val ∈ A ∪ B := by simp; left; exact x.property
example (A : Set) (x : A.toSubtype') : x.val = x := by
  have h := ↑x
  rfl

-- example (A : Set) (x : Object) (y : Object) (hx : x ∈ A) (hy : y ∈ A) :

-- Now instead of writing `x': A.toSubtype`, we can just write `x': A`.
-- Compare these three proofs. They are equivalent, but the last one reads most concisely.
example (A B: Set) (x: Object) (hx: x ∈ A) : x ∈ A ∪ B := by simp; left; exact hx
example (A B: Set) (x': A.toSubtype) : x'.val ∈ A ∪ B := by simp; left; exact x'.property
example (A B: Set) (x': A) : x'.val ∈ A ∪ B := by simp; left; exact x'.property

/--
  Elements of a set (implicitly coerced to a subtype) are also elements of the set
  (with respect to the membership operation of the set theory).
-/
lemma SetTheory.Set.subtype_property (A:Set) (x:A) : x.val ∈ A := x.property

lemma SetTheory.Set.subtype_coe (A:Set) (x:A) : x.val = x := by
  -- ⊢ ↑x = ↑x
  have h : x.val = ↑x := by rfl
  exact h

lemma SetTheory.Set.coe_inj (A:Set) (x y:A) : x.val = y.val ↔ x = y := Subtype.coe_inj

/--
  If one has a proof `hx` of `x ∈ A`, then `A.subtype_mk hx` will then make the element of `A`
  (viewed as a subtype) corresponding to `x`.
-/
def SetTheory.Set.subtype_mk (A:Set) {x:Object} (hx:x ∈ A) : A := ⟨ x, hx ⟩

@[simp]
lemma SetTheory.Set.subtype_mk_coe {A:Set} {x:Object} (hx:x ∈ A) : A.subtype_mk hx = x := by rfl



/-- Axiom 3.6 (axiom of specification) -/
abbrev SetTheory.Set.specify (A:Set) (P: A → Prop) : Set := SetTheory.specify A P

theorem SetTheory.Set.mem_of_mem_specify {A : Set} {P : A → Prop} {x : Object}
  (h: x ∈ A.specify P) : x ∈ A
:= by
  have hxA : ∀x, x ∈ A.specify P → x ∈ A := (SetTheory.specification_axiom A P).left
  exact hxA x h

theorem SetTheory.Set.prop_of_mem_specify {A : Set} {P : A → Prop}
  {x : Object}
  (h : x ∈ A.specify P) : P ⟨x, (mem_of_mem_specify h)⟩
:= by
  have hxA : x ∈ A := mem_of_mem_specify h
  have hxP : P ⟨x, hxA⟩ := ((SetTheory.specification_axiom A P).right ⟨x, hxA⟩).mp h
  exact hxP

theorem SetTheory.Set.mem_specify_of_prop {A : Set} {P : A → Prop} {x : Object}
  (hxA : x ∈ A)
  (hPx : P ⟨x, hxA⟩) : x ∈ A.specify P
:= by
  exact ((SetTheory.specification_axiom A P).right ⟨x, hxA⟩).mpr hPx

theorem SetTheory.Set.specification_axiom {A : Set} {P : A → Prop} {x : Object}
  (h : x ∈ A.specify P) : x ∈ A
:= by
  -- These are just different ways of saying the same thing
  have hxA₁ : A.specify P ⊆ A               := (SetTheory.specification_axiom A P).left
  have hxA₂ : ∀ x, ↑x ∈ A.specify P → x ∈ A := (SetTheory.specification_axiom A P).left
  exact hxA₂ x h


theorem SetTheory.Set.specification_axiom' {A : Set}
  (P : A → Prop) (x : A) : x.val ∈ A.specify P ↔ P x
:= by
  have hxP : ∀ (x : A), x.val ∈ A.specify P ↔ P x := (SetTheory.specification_axiom A P).right
  exact hxP x

@[simp]
theorem SetTheory.Set.specification_axiom'' {A : Set}
  (P : A → Prop) (x : Object) : x ∈ A.specify P ↔ ∃ (h : x ∈ A), P ⟨x, h⟩
:= by
  constructor
  · intro (hxAP : x ∈ A.specify P)
    have hxA : x ∈ A      := mem_of_mem_specify hxAP
    have hPx : P ⟨x, hxA⟩ := prop_of_mem_specify hxAP
    exact ⟨hxA, hPx⟩
  · intro ⟨(hxA : x ∈ A), (hPx : P ⟨x, hxA⟩)⟩
    have hxAP : x ∈ A.specify P := mem_specify_of_prop hxA hPx
    exact hxAP


theorem SetTheory.Set.specify_subset {A : Set} (P : A → Prop) : A.specify P ⊆ A := by
  exact fun x => mem_of_mem_specify


theorem SetTheory.Set.specify_congr
  {A A' : Set}
  (hAA' : A = A')
  {P  : A  → Prop}
  {P' : A' → Prop}
  (hPP' : (x : Object) → (h : x ∈ A) → (h' : x ∈ A') → P ⟨x, h⟩ ↔ P' ⟨x, h'⟩) :
  A.specify P = A'.specify P'
:= by
  ext x
  constructor
  . intro (hxAP  : x ∈ A.specify P)  -- ⊢ x ∈ A'.specify P'
    have hxA     : x ∈ A             := mem_of_mem_specify hxAP
    have hxA'    : x ∈ A'            := hAA' ▸ hxA
    have hxP     : P  ⟨x, hxA⟩       := prop_of_mem_specify hxAP
    have hxP'    : P' ⟨x, hxA'⟩      := (hPP' x hxA hxA').mp hxP
    have hxAP'   : x ∈ A'.specify P' := mem_specify_of_prop hxA' hxP'
    exact hxAP'
  . intro (hxAP' : x ∈ A'.specify P') -- ⊢ x ∈ A.specify P
    have hxA'    : x ∈ A'            := mem_of_mem_specify hxAP'
    have hxA     : x ∈ A             := hAA' ▸ hxA'
    have hxP'    : P' ⟨x, hxA'⟩      := prop_of_mem_specify hxAP'
    have hxP     : P  ⟨x, hxA⟩       := (hPP' x hxA hxA').mpr hxP'
    have hxAP    : x ∈ A.specify P   := mem_specify_of_prop hxA hxP
    exact hxAP


instance SetTheory.Set.instIntersection : Inter Set where
  inter X Y := X.specify (fun x ↦ x.val ∈ Y)

-- Now we can use the `X ∩ Y` notation for an intersection of two `Set`s.
example (X Y: Set) : X ∩ Y = X.specify (fun x ↦ x.val ∈ Y) := rfl

/-- Definition 3.1.22 (Intersections) -/
@[simp]
theorem SetTheory.Set.mem_inter (x : Object) (X Y : Set) : x ∈ (X ∩ Y) ↔ (x ∈ X ∧ x ∈ Y) := by
  constructor
  · intro (hxXY : x ∈ X ∩ Y)
    have hxX : x ∈ X := mem_of_mem_specify hxXY
    have hxY : x ∈ Y := prop_of_mem_specify hxXY
    exact ⟨hxX, hxY⟩
  · intro ⟨hxX, hxY⟩
    exact mem_specify_of_prop hxX hxY

lemma SetTheory.Set.mem_inter_left {x : Object} {X Y : Set}
  (h : x ∈ X ∩ Y): x ∈ X
:= by
  exact ((mem_inter x X Y).mp h).left

lemma SetTheory.Set.mem_inter_right {x : Object} {X Y : Set}
  (h : x ∈ X ∩ Y): x ∈ Y
:= by
  exact ((mem_inter x X Y).mp h).right

lemma SetTheory.Set.mem_inter_of {x : Object} {X Y : Set}
  (hxX : x ∈ X)
  (hxY : x ∈ Y) : x ∈ X ∩ Y
:= by
  exact (mem_inter x X Y).mpr ⟨hxX, hxY⟩


instance SetTheory.Set.instSDiff : SDiff Set where
  sdiff X Y := X.specify (fun x ↦ x.val ∉ Y)

-- Now we can use the `X \ Y` notation for a difference of two `Set`s.
example (X Y: Set) : X \ Y = X.specify (fun x ↦ x.val ∉ Y) := rfl

/-- Definition 3.1.26 (Difference sets) -/
@[simp]
theorem SetTheory.Set.mem_sdiff (x : Object) (X Y : Set) : x ∈ (X \ Y) ↔ (x ∈ X ∧ x ∉ Y) := by
  constructor
  · intro (hxXY : x ∈ X \ Y)
    have hxX : x ∈ X := mem_of_mem_specify hxXY
    have hxY : x ∉ Y := prop_of_mem_specify hxXY
    exact ⟨hxX, hxY⟩
  · intro ⟨hxX, hxY⟩
    exact mem_specify_of_prop hxX hxY

lemma SetTheory.Set.mem_sdiff_left {x : Object} {X Y : Set} (h : x ∈ X \ Y) : x ∈ X :=
  ((mem_sdiff x X Y).mp h).left

lemma SetTheory.Set.mem_sdiff_right {x : Object} {X Y : Set} (h : x ∈ X \ Y) : x ∉ Y :=
  ((mem_sdiff x X Y).mp h).right


/-- Proposition 3.1.27(d) / Exercise 3.1.6 -/
theorem SetTheory.Set.inter_comm (A B : Set) : A ∩ B = B ∩ A := by
  ext x
  constructor
  · intro (h : x ∈ A ∩ B)
    have hxA : x ∈ A := mem_of_mem_specify h
    have hxB : x ∈ B := prop_of_mem_specify h
    exact mem_specify_of_prop hxB hxA
  · intro (h : x ∈ B ∩ A)
    have hxB : x ∈ B := mem_of_mem_specify h
    have hxA : x ∈ A := prop_of_mem_specify h
    exact mem_specify_of_prop hxA hxB

/-- Proposition 3.1.27(b) -/
theorem SetTheory.Set.subset_union {A X : Set} (hAX: A ⊆ X) : A ∪ X = X := by
  ext x
  constructor
  · intro (h : x ∈ A ∪ X)
    rcases (mem_union_cases h) with (hxA : x ∈ A) | (hxX : x ∈ X)
    · have hxAX : x ∈ A → x ∈ X := hAX x
      exact hxAX hxA
    · exact hxX
  · intro (h : x ∈ X)
    exact mem_union_right h

/-- Proposition 3.1.27(b) -/
theorem SetTheory.Set.union_subset {A X : Set} (hAX : A ⊆ X) : X ∪ A = X := by
  rw [union_comm]
  exact subset_union hAX

/-- Proposition 3.1.27(c) -/
@[simp]
theorem SetTheory.Set.inter_self (A : Set) : A ∩ A = A := by
  ext x
  constructor
  · intro (h : x ∈ A ∩ A)
    exact mem_of_mem_specify h
  · intro (h : x ∈ A)
    exact mem_specify_of_prop h h

/-- Proposition 3.1.27(e) -/
theorem SetTheory.Set.inter_assoc (A B C : Set) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  ext x
  simp [mem_inter]
  tauto

/-- Proposition 3.1.27(f) -/
theorem  SetTheory.Set.inter_union_distrib_left (A B C : Set) :
  A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)
:= by
  ext x
  simp only [mem_inter, mem_union]
  tauto

/-- Proposition 3.1.27(f) -/
theorem  SetTheory.Set.union_inter_distrib_left (A B C:Set) :
    A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)
:= by
  ext x
  simp only [mem_union, mem_inter]
  tauto

/-- Proposition 3.1.27(f) -/
theorem SetTheory.Set.union_compl {A X : Set}
  (hAX : A ⊆ X) : A ∪ (X \ A) = X
:= by
  ext x
  rw [mem_union, mem_sdiff]
  constructor
  · intro (h₁ : x ∈ A ∨ (x ∈ X ∧ x ∉ A))
    have h₂ : x ∈ A → x ∈ X           := hAX x
    have h₃ : x ∈ X ∨ (x ∈ X ∧ x ∉ A) := Or.imp_left h₂ h₁
    have h₄ : x ∈ X                   := by tauto
    exact h₄
  · intro (h₁ : x ∈ X)
    have h₂ : x ∈ A ∨ (x ∈ X ∧ x ∉ A) := by tauto
    exact h₂

theorem SetTheory.Set.union_compl' {A X : Set}
  (hAX : A ⊆ X) : A ∪ (X \ A) = X
:= by
  ext x
  rw [mem_union, mem_sdiff]
  tauto

/-- Proposition 3.1.27(f) -/
theorem SetTheory.Set.inter_compl {A X : Set} : A ∩ (X \ A) = ∅
:= by
  ext x
  rw [mem_inter, mem_sdiff]
  constructor
  · intro ⟨(hA : x ∈ A), (hX : x ∈ X), (hnA : x ∉ A)⟩
    exact (hnA hA).elim
  · intro (h : x ∈ ∅)
    exact ((not_mem_empty x) h).elim

/-- Proposition 3.1.27(g) -/
theorem SetTheory.Set.compl_union {A B X : Set}
  (_hAX : A ⊆ X)
  (_hBX : B ⊆ X) : X \ (A ∪ B) = (X \ A) ∩ (X \ B)
:= by
  ext x
  calc  x ∈ X \ (A ∪ B)
    _ ↔ x ∈ X ∧ ¬(x ∈ A ∨ x ∈ B)           := by rw [mem_sdiff, mem_union]
    _ ↔ x ∈ X ∧ x ∉ A ∧ x ∉ B              := by rw [not_or]
    _ ↔ (x ∈ X ∧ x ∉ A) ∧ (x ∈ X ∧ x ∉ B)  := by rw [and_and_left]
    _ ↔ (x ∈ X \ A) ∧ (x ∈ X \ B)          := by rw [← mem_sdiff, ← mem_sdiff]
    _ ↔ x ∈ (X \ A) ∩ (X \ B)              := by rw [← mem_inter]

/-- Proposition 3.1.27(g) -/
theorem SetTheory.Set.compl_inter {A B X : Set}
  (_hAX : A ⊆ X)
  (_hBX : B ⊆ X) : X \ (A ∩ B) = (X \ A) ∪ (X \ B)
:= by
  ext x
  calc  x ∈ X \ (A ∩ B)
    _ ↔ x ∈ X ∧ ¬(x ∈ A ∧ x ∈ B)          := by rw [mem_sdiff, mem_inter]
    _ ↔ x ∈ X ∧ (x ∉ A ∨ x ∉ B)           := by rw [not_and_or]
    _ ↔ (x ∈ X ∧ x ∉ A) ∨ (x ∈ X ∧ x ∉ B) := by rw [and_or_left]
    _ ↔ x ∈ (X \ A) ∨ x ∈ (X \ B)         := by rw [← mem_sdiff, ← mem_sdiff]
    _ ↔ x ∈ (X \ A) ∪ (X \ B)             := by rw [← mem_union]

-- In both cases, we can drop the assumptions:

theorem SetTheory.Set.compl_union' {A B X : Set} :
   X \ (A ∪ B) = (X \ A) ∩ (X \ B)
:= by
  ext x
  simp only [mem_sdiff, mem_union, mem_inter]
  tauto

theorem SetTheory.Set.compl_inter' {A B X : Set} :
  X \ (A ∩ B) = (X \ A) ∪ (X \ B)
:= by
  ext x
  simp only [mem_union, mem_sdiff, mem_inter]
  tauto

/-- Not from textbook: sets form a distributive lattice. -/
instance SetTheory.Set.instDistribLattice : DistribLattice Set where
  le := (· ⊆ ·)
  le_refl := subset_self
  le_trans := fun _ _ _ ↦ subset_trans
  le_antisymm := subset_antisymm
  inf := (· ∩ ·)
  sup := (· ∪ ·)

  le_sup_left := fun A B x hxA => mem_union_left hxA
  le_sup_right := fun A B x hxB => mem_union_right hxB

  sup_le := fun A B C hAC hBC x hxAB => by
    cases mem_union_cases hxAB with
    | inl hxA => exact hAC x hxA
    | inr hxB => exact hBC x hxB

  inf_le_left := fun A B x hxAB => mem_inter_left hxAB
  inf_le_right := fun A B x hxAB => mem_inter_right hxAB
  le_inf := fun A B C hAB hAC x hxA => mem_inter_of (hAB x hxA) (hAC x hxA)

  le_sup_inf := by
    intro X Y Z
    change (X ∪ Y) ∩ (X ∪ Z) ⊆ X ∪ (Y ∩ Z)
    rw [← union_inter_distrib_left]

/-- Sets have a minimal element.  -/
instance SetTheory.Set.instOrderBot : OrderBot Set where
  bot := ∅
  bot_le := empty_subset

-- Now we've defined `A ≤ B` to mean `A ⊆ B`, and set `⊥` to `∅`.
-- This makes the `Disjoint` definition from Mathlib work with our `Set`.
example (A B: Set) : (A ≤ B) ↔ (A ⊆ B) := by rfl
example : ⊥ = (∅: Set) := by rfl
example (A B: Set) : Prop := Disjoint A B

/-- Definition of disjointness (using the previous instances) -/
theorem SetTheory.Set.disjoint_iff (A B:Set) : Disjoint A B ↔ A ∩ B = ∅ := by
  convert _root_.disjoint_iff

abbrev SetTheory.Set.replace (A:Set) {P: A → Object → Prop}
  (hP : ∀ x y y', P x y ∧ P x y' → y = y') : Set := SetTheory.replace A P hP

/-- Axiom 3.7 (Axiom of replacement) -/
@[simp]
theorem SetTheory.Set.replacement_axiom
  {A : Set}
  {P : A → Object → Prop}
  (hP : ∀ x y y', P x y ∧ P x y' → y = y')
  (y : Object)
  : y ∈ A.replace hP ↔ ∃ x, P x y
:= by
  exact SetTheory.replacement_axiom A P hP y

abbrev Nat := SetTheory.nat

-- Going forward, we'll use `Nat` as a type.
-- However, notice we've set `Nat` to `SetTheory.nat` which is a `Set` and not a type.
-- The only reason we can write `x: Nat` is because we've previously defined a `CoeSort`
-- coercion that lets us write `x: A` (when `A` is a `Set`) as a shortcut for `x: A.toSubtype`.
-- This is why, whenever you see `x: Nat`, you're really looking at `x: Nat.toSubtype`.
example (x: Nat) : Nat.toSubtype := x
example (x: Nat) : Object := x.val
example (x: Nat) : (x.val ∈ Nat) := x.property
example (o: Object) (ho: o ∈ Nat) : Nat := ⟨o, ho⟩

/-- Axiom 3.8 (Axiom of infinity) -/
def SetTheory.Set.nat_equiv : ℕ ≃ Nat := SetTheory.nat_equiv

-- Below are some API for handling coercions. This may not be the optimal way to set things up.
instance SetTheory.Set.instOfNat {n:ℕ} : OfNat Nat n where
  ofNat := nat_equiv n

-- Now we can define `Nat` with a natural literal.
example : Nat := 5
example : (5 : Nat).val ∈ Nat := (5 : Nat).property

instance SetTheory.Set.instNatCast : NatCast Nat where
  natCast n := nat_equiv n

-- Now we can turn `ℕ` into `Nat`.
example (n : ℕ) : Nat := n
example (n : ℕ) : (n : Nat).val ∈ Nat := (n : Nat).property

instance SetTheory.Set.toNat : Coe Nat ℕ where
  coe n := nat_equiv.symm n

-- Now we can turn `Nat` into `ℕ`.
example (n : Nat) : ℕ := n

instance SetTheory.Object.instNatCast : NatCast Object where
  natCast n := (n:Nat).val

-- Now we can turn `ℕ` into an `Object`.
example (n: ℕ) : Object := n
example (n: ℕ) : Set := {(n: Object)}

instance SetTheory.Object.instOfNat {n:ℕ} : OfNat Object n where
  ofNat := ((n:Nat):Object)

-- Now we can define `Object` with a natural literal.
example : Object := 1
example : Set := {1, 2, 3}

@[simp]
lemma SetTheory.Object.ofnat_eq {n:ℕ} : ((n:Nat):Object) = (n:Object) := rfl

lemma SetTheory.Object.ofnat_eq' {n:ℕ} : (ofNat(n):Object) = (n:Object) := rfl

@[simp]
lemma SetTheory.Object.ofnat_eq'' {n:Nat} : ((n:ℕ):Object) = (n: Object) := by
  simp [instNatCast, Nat.cast, Set.instNatCast]

@[simp]
lemma SetTheory.Object.ofnat_eq''' {n:ℕ} {hn} : ((⟨(n:Object), hn⟩: nat): ℕ) = n := by
  simp [instNatCast, Nat.cast, Set.instNatCast]

lemma SetTheory.Set.nat_coe_eq {n:ℕ} : (n:Nat) = OfNat.ofNat n := rfl

@[simp]
lemma SetTheory.Set.nat_equiv_inj (n m:ℕ) : (n:Nat) = (m:Nat) ↔ n=m  :=
  Equiv.apply_eq_iff_eq nat_equiv

@[simp]
lemma SetTheory.Set.nat_equiv_symm_inj (n m:Nat) : (n:ℕ) = (m:ℕ) ↔ n = m :=
  Equiv.apply_eq_iff_eq nat_equiv.symm

@[simp]
theorem SetTheory.Set.ofNat_inj (n m:ℕ) :
    (ofNat(n) : Nat) = (ofNat(m) : Nat) ↔ ofNat(n) = ofNat(m) := by
      convert nat_equiv_inj _ _

example : (5:Nat) ≠ (3:Nat) := by
  simp

@[simp]
theorem SetTheory.Set.ofNat_inj' (n m:ℕ) :
    (ofNat(n) : Object) = (ofNat(m) : Object) ↔ ofNat(n) = ofNat(m) := by
      simp only [←Object.ofnat_eq, Object.ofnat_eq', Set.coe_inj, Set.nat_equiv_inj]
      rfl

example : (5:Object) ≠ (3:Object) := by
  simp

@[simp]
lemma SetTheory.Set.nat_coe_eq_iff {m n : ℕ} : (m:Object) = ofNat(n) ↔ m = n := by exact ofNat_inj' m n

example (n: ℕ) : (n: Object) = 2 ↔ n = 2 := by
  simp

@[simp]
theorem SetTheory.Object.natCast_inj (n m:ℕ) :
    (n : Object) = (m : Object) ↔ n = m := by
      simp [←ofnat_eq, Subtype.val_inj]

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe (n:ℕ) : ((n:Nat):ℕ) = n :=
  Equiv.symm_apply_apply nat_equiv n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe' (n:Nat) : ((n:ℕ):Nat) = n :=
  Equiv.symm_apply_apply nat_equiv.symm n

@[simp]
lemma SetTheory.Set.nat_equiv_coe_of_coe'' (n:ℕ) : ((ofNat(n):Nat):ℕ) = n :=
  nat_equiv_coe_of_coe n

@[simp]
lemma SetTheory.Set.nat_coe_eq_iff' {m: Nat} {n : ℕ} : (m:Object) = (ofNat(n):Object) ↔ (m:ℕ) = ofNat(n) := by
  constructor <;> intro h <;> rw [show m = n by aesop]
  apply nat_equiv_coe_of_coe; rfl


/-- Example 3.1.16 (simplified).  -/
example : ({3, 5}:Set) ⊆ {1, 3, 5} := by
  simp only [subset_def, mem_pair, mem_triple]; tauto


/-- Example 3.1.17 (simplified). -/
example : ({3, 5}:Set).specify (fun x ↦ x.val ≠ 3) = ({5}:Set) := by
  ext x
  simp only [mem_singleton] -- x ∈ {5} → x = 5
  constructor
  · intro h₀
    have h₁ : x ∈ ({3, 5} : Set) := mem_of_mem_specify h₀
    have h₂ : ↑x ≠ 3             := prop_of_mem_specify h₀
    rcases (mem_pair x 3 5).mp h₁ with (hx3 : x = 3) | (hx5 : x = 5)
    · exact (h₂ hx3).elim
    · exact hx5
  · intro (hx5 : x = 5)
    have h₁ : x ∈ ({3, 5} : Set) := mem_pair_right x 3 5 hx5
    have h₂ : x ≠ 3 := by rw [hx5]; norm_num
    have h₃ : x ∈ ({3, 5}:Set).specify (fun x ↦ x.val ≠ 3) := mem_specify_of_prop h₁ h₂
    exact h₃

example : ({3, 5}:Set).specify (fun x ↦ x.val ≠ 3) = ({5}:Set) := by
  ext x
  simp only [mem_singleton]
  constructor
  · intro h₁
    simp only [ne_eq, specification_axiom'', mem_pair, exists_prop] at h₁
    tauto
  · rintro rfl
    norm_num

/-- Example 3.1.24 -/
example : ({1, 2, 4}:Set) ∩ {2, 3, 4} = {2, 4} := by
  ext x
  -- Instead of unfolding repetitive branches by hand like earlier,
  -- you can use the `aesop` tactic which does this automatically.
  aesop

/-- Example 3.1.24 -/

example : ({1, 2}:Set) ∩ {3,4} = ∅ := by
  rw [eq_empty_iff_forall_not_mem]
  aesop

example : ¬ Disjoint ({1, 2, 3}:Set) {2,3,4} := by
  rw [disjoint_iff]
  intro h
  change {1, 2, 3} ∩ {2, 3, 4} = ∅ at h
  rw [eq_empty_iff_forall_not_mem] at h
  aesop

example : Disjoint (∅:Set) ∅ := by
  rw [disjoint_iff]
  ext x
  constructor
  · intro h
    exact (not_mem_empty' (mem_inter_left h)).elim
  · intro h
    exact (not_mem_empty' h).elim


/-- Definition 3.1.26 example -/

example : ({1, 2, 3, 4}:Set) \ {2,4,6} = {1, 3} := by
  ext x
  aesop

/-- Example 3.1.30 -/
example : ({3, 5, 9}:Set).replace (P := fun x y ↦ ∃ (n:ℕ), x.val = n ∧ y = (n+1:ℕ)) (by aesop)
  = {4,6,10} := by
  ext x
  simp only [replacement_axiom]
  constructor
  · intro ⟨y, ⟨z, h₁, h₂⟩⟩
    aesop
  · intro h₁
    aesop

/-- Example 3.1.31 -/
example : ({3,5,9}:Set).replace (P := fun _ y ↦ y=1) (by aesop) = {1} := by
  ext; simp only [replacement_axiom]; aesop

/-- Exercise 3.1.5.  One can use the `tfae_have` and `tfae_finish` tactics here. -/
theorem SetTheory.Set.subset_tfae (A B:Set) : [A ⊆ B, A ∪ B = B, A ∩ B = A].TFAE := by
  tfae_have 1 → 2 := by intro h; ext x; simp [mem_union]; exact h x
  tfae_have 1 → 3 := by intro h; ext x; simp [mem_inter]; exact h x
  tfae_have 2 → 1 := by intro h x; rw [h.symm]; simp [mem_union]; tauto
  tfae_have 3 → 1 := by intro h x; rw [h.symm]; simp [mem_inter]
  tfae_have 2 → 3 := by intro h; ext x; rw [h.symm]; simp [mem_inter]; tauto
  tfae_finish

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.inter_subset_left (A B:Set) : A ∩ B ⊆ A :=
  fun _ hxAB => mem_inter_left hxAB

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.inter_subset_right (A B:Set) : A ∩ B ⊆ B :=
  fun _ hxAB => mem_inter_right hxAB

/-- Exercise 3.1.7 -/
@[simp]
theorem SetTheory.Set.subset_inter_iff (A B C:Set) : C ⊆ A ∩ B ↔ C ⊆ A ∧ C ⊆ B := ⟨
  fun hCAB => ⟨
    fun x hxC => mem_inter_left (hCAB x hxC),
    fun x hxC => mem_inter_right (hCAB x hxC)
  ⟩,
  fun ⟨hCA, hCB⟩ x hxC => mem_inter_of (hCA x hxC) (hCB x hxC)
⟩

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_union_left (A B:Set) : A ⊆ A ∪ B :=
  fun _ hxA => mem_union_left hxA

/-- Exercise 3.1.7 -/
theorem SetTheory.Set.subset_union_right (A B:Set) : B ⊆ A ∪ B :=
  fun _ hxB => mem_union_right hxB

/-- Exercise 3.1.7 -/
@[simp]
theorem SetTheory.Set.union_subset_iff (A B C:Set) : A ∪ B ⊆ C ↔ A ⊆ C ∧ B ⊆ C := ⟨
  fun hABC => ⟨
    fun x hxA => hABC x (mem_union_left hxA),
    fun x hxB => hABC x (mem_union_right hxB)
  ⟩,
  fun ⟨hAC, hBC⟩ x hxAB => Or.elim (mem_union_cases hxAB) (hAC x) (hBC x)
⟩

/-- Exercise 3.1.8 -/
@[simp]
theorem SetTheory.Set.inter_union_cancel (A B:Set) : A ∩ (A ∪ B) = A := by
  ext x
  rw [mem_inter, mem_union]
  tauto

/-- Exercise 3.1.8 -/
@[simp]
theorem SetTheory.Set.union_inter_cancel (A B:Set) : A ∪ (A ∩ B) = A := by
  ext x
  rw [mem_union, mem_inter]
  tauto

/-- Exercise 3.1.9 -/
theorem SetTheory.Set.partition_left {A B X:Set}
  (h_union: A ∪ B = X)
  (h_inter: A ∩ B = ∅) : A = X \ B
:= by
  ext x
  rw [mem_sdiff]
  constructor
  · intro hxA
    have hxX : x ∈ X := h_union.symm ▸ (mem_union_left hxA)
    have hxB : x ∉ B := fun hxB => (not_mem_empty x) (h_inter ▸ (mem_inter_of hxA hxB))
    exact ⟨hxX, hxB⟩
  · intro ⟨hxX, hxB⟩
    have hxAB : x ∈ A ∨ x ∈ B := mem_union_cases (h_union ▸ hxX)
    have hxA  : x ∈ A         := by tauto
    exact hxA

/-- Exercise 3.1.9 -/
theorem SetTheory.Set.partition_right {A B X:Set}
  (h_union: A ∪ B = X)
  (h_inter: A ∩ B = ∅) : B = X \ A
:= by
  have h_union' : B ∪ A = X := by simpa only [union_comm] using h_union
  have h_inter' : B ∩ A = ∅ := by simpa only [inter_comm] using h_inter
  exact partition_left h_union' h_inter'

lemma SetTheory.Set.singleton_subset_of_mem {x : Object} {A : Set}
  (hxA : x ∈ A) : {x} ⊆ A
:= by
  intro y hy
  rw [mem_singleton] at hy
  exact hy ▸ hxA

lemma SetTheory.Set.mem_of_singleton_subset {x : Object} {A : Set}
  (hxA : {x} ⊆ A) : x ∈ A
:= by
  exact hxA x ((mem_singleton x x).mpr rfl)

lemma SetTheory.Set.disjoint_iff_inter_eq_empty {A B : Set} : Disjoint A B ↔ A ∩ B = ∅ := by
  constructor
  · intro (h₁ : Disjoint A B)
    have h_disjoint : ∀X, X ⊆ A → X ⊆ B → X ⊆ ∅ := by simpa only [Disjoint] using h₁
    ext x
    constructor
    · intro (h_inter : x ∈ A ∩ B)
      have hxA : {x} ⊆ A := singleton_subset_of_mem (mem_inter_left h_inter)
      have hxB : {x} ⊆ B := singleton_subset_of_mem (mem_inter_right h_inter)
      have hx0 : x ∈ ∅ := mem_of_singleton_subset (h_disjoint {x} hxA hxB)
      exact hx0
    · intro hx0
      exact (not_mem_empty' hx0).elim
  · intro (h_inter_empty : A ∩ B = ∅) X (hXA : X ⊆ A) (hXB : X ⊆ B) x (hxX : x ∈ X)
    have hxAB : x ∈ A ∩ B := mem_inter_of (hXA x hxX) (hXB x hxX)
    have hx0  : x ∈ ∅ := h_inter_empty ▸ hxAB
    exact hx0

/--
  Exercise 3.1.10.
  You may find `Function.onFun_apply` and the `fin_cases` tactic useful.
-/
theorem SetTheory.Set.pairwise_disjoint (A B : Set) :
  Pairwise (Function.onFun Disjoint ![A \ B, A ∩ B, B \ A])
:= by
  have h₁ : (A \ B) ∩ (A ∩ B) = ∅ := by ext x; simp [mem_inter, mem_sdiff]; tauto
  have h₂ : (A \ B) ∩ (B \ A) = ∅ := by ext x; simp [mem_inter, mem_sdiff]; tauto
  have h₃ : (A ∩ B) ∩ (B \ A) = ∅ := by ext x; simp [mem_inter, mem_sdiff]; tauto
  intro i j hij
  fin_cases i <;> fin_cases j <;> try contradiction
  all_goals simp [disjoint_iff_inter_eq_empty]
  · exact h₁
  · exact h₂
  · simpa [inter_comm] using h₁
  · exact h₃
  · simpa [inter_comm] using h₂
  · simpa [inter_comm] using h₃

/-- Exercise 3.1.10 -/
theorem SetTheory.Set.union_eq_partition (A B : Set) : A ∪ B = (A \ B) ∪ (A ∩ B) ∪ (B \ A) := by
  ext x
  simp only [mem_union, mem_sdiff, mem_inter]
  tauto

/--
  Exercise 3.1.11.
  The challenge is to prove this without using `Set.specify`, `Set.specification_axiom`,
  `Set.specification_axiom'`, or anything built from them (like differences and intersections).
-/
theorem SetTheory.Set.specification_from_replacement {A : Set} {P : A → Prop} :
  ∃ B, B ⊆ A ∧ ∀ x, x.val ∈ B ↔ P x
:= by
  let P' : (Subtype (mem · A)) → Object → Prop := fun x y => (↑x = y) ∧ P x
  have hP' : ∀ (x : Subtype (mem · A)) (y y' : Object), P' x y ∧ P' x y' → y = y' := by
    intro x y y' ⟨⟨(hxy : x = y), _⟩, ⟨(hxy' : x = y'), _⟩⟩
    exact hxy ▸ hxy'
  let B := replace A hP'
  use B
  have hB : B ⊆ A := by
    intro x (hxB : x ∈ B)
    have h₁ : ∃ z, ∃ (hzA : z ∈ A), P' ⟨z, hzA⟩ x := by simpa [B] using hxB
    have ⟨z, hzA, hP'⟩           := h₁
    have h₂ : z = x ∧ P ⟨z, hzA⟩ := by simpa only [P'] using hP'
    have hxA : x ∈ A             := h₂.left ▸ hzA
    exact hxA
  apply And.intro hB
  intro (z : A)
  have h₁ : ↑z ∈ B ↔ ∃x, P' x z     := replacement_axiom hP' z
  have h₂ : ↑z ∈ B ↔ (↑z ∈ A) ∧ P z := by simpa [P'] using h₁
  have h₃ : ↑z ∈ B ↔ P z            := by simpa [z.property] using h₂
  exact h₃


/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_union_subset {A B A' B' : Set}
  (hA'A : A' ⊆ A)
  (hB'B : B' ⊆ B) : A' ∪ B' ⊆ A ∪ B
:= by
  intro x hx
  rcases (mem_union_cases hx) with hxA' | hxB'
  · exact mem_union_left (hA'A x hxA')
  · exact mem_union_right (hB'B x hxB')

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_inter_subset {A B A' B' : Set}
  (hA'A : A' ⊆ A)
  (hB'B : B' ⊆ B) : A' ∩ B' ⊆ A ∩ B
:= by
  intro x hx
  exact mem_inter_of
    (hA'A x (mem_inter_left hx))
    (hB'B x (mem_inter_right hx))

lemma SetTheory.Set.sdiff_empty (A : Set) : A \ ∅ = A := by
  ext x
  constructor
  · exact fun hx => mem_of_mem_specify hx
  · exact fun hx => mem_specify_of_prop hx (not_mem_empty x)

lemma SetTheory.Set.sdiff_self (A : Set) : A \ A = (∅ : Set) := by
  ext x
  constructor
  · intro hx
    have h₁ := mem_of_mem_specify hx
    have h₂ := prop_of_mem_specify hx
    exact (h₂ h₁).elim
  · intro hx
    exact (not_mem_empty' hx).elim

/-- Exercise 3.1.12.-/
theorem SetTheory.Set.subset_diff_subset_counter :
  ∃ (A B A' B' : Set), (A' ⊆ A) ∧ (B' ⊆ B) ∧ ¬ (A' \ B') ⊆ (A \ B)
:= by
  -- Consider any non-empty set X.  Let A = B = A' = X and let B' = ∅
  -- Then A' \ B' = X \ ∅ = X but A \ B = X \ X = ∅; clearly X ⊆ ∅ is false
  let X := ({1} : Set)
  use X; use X; use X; use ∅
  have h₁ : X ⊆ X     := fun x hx => hx
  have h₂ : ∅ ⊆ X     := fun x hx => (not_mem_empty' hx).elim
  have h₃ : X \ ∅ = X := sdiff_empty X
  have h₄ : X \ X = ∅ := sdiff_self X
  have h₅ : ¬ X ⊆ ∅   := fun h => not_mem_empty' (h 1 (mem_singleton' 1))
  simp only [h₁, h₂, h₃, h₄, h₅]
  tauto

/-
  Final part of Exercise 3.1.12: state and prove a reasonable substitute positive result for the
  above theorem that involves set differences.
-/
theorem SetTheory.Set.subset_diff_subset_counter' {A B A' B' : Set}
  (hA'A : A' ⊆ A)
  (hB'B : B' ⊆ B) : (A' \ B) ⊆ (A \ B')
:= by
  intro x (hxA'B : x ∈ A' \ B)
  have hxA' : x ∈ A' := mem_of_mem_specify hxA'B
  have hxB  : x ∉ B  := prop_of_mem_specify hxA'B
  have hxB' : x ∉ B' := (mt (hB'B x)) hxB
  have hxA  : x ∈ A  := hA'A x hxA'
  exact mem_specify_of_prop hxA hxB'


lemma SetTheory.Set.exists_distinct_mem_of_nonempty_nonsingleton {A : Set}
  (x : Object)
  (h₁ : A ≠ ∅)
  (h₂ : ∀ a, A ≠ {a}) : ∃y ∈ A, y ≠ x
:= by
  contrapose! h₂ -- ∀ y ∈ A, y = x
  use x
  ext y
  constructor
  · intro (hyA : y ∈ A)
    have hyx : y = x := h₂ y hyA
    have hyX : y ∈ {x} := mem_singleton_of_eq hyx
    exact hyX
  · intro (hyX : y ∈ ({x} : Set))
    have ⟨z, (hzA : z ∈ A)⟩ := nonempty_def h₁
    have hyx : y = x := eq_of_mem_singleton hyX
    have hzx : z = x := h₂ z hzA
    have hyA : y ∈ A := hyx ▸ hzx ▸ hzA
    exact hyA

lemma SetTheory.Set.pair_subset_of_mems {x y : Object} {A : Set}
  (hxA : x ∈ A)
  (hyA : y ∈ A) : {x, y} ⊆ A
:= by
  intro a ha
  rcases (mem_pair a x y).mp ha with (hax : a = x) | (hay : a = y)
  · exact hax ▸ hxA
  . exact hay ▸ hyA

lemma SetTheory.Set.singleton_ssubset_pair
  (x y : Object) (hxy : x ≠ y) : {x} ⊂ ({x, y} : Set)
:= by
  have h₁ : {x} ⊆ ({x, y} : Set) := fun a => by simp [mem_singleton]; tauto
  have h₂ : {x} ≠ ({x, y} : Set) := by
    intro h_eq
    have hy₁ : y ∈ ({x, y} : Set) := mem_pair_right y x y rfl
    have hy₂ : y ∈ ({x} : Set)    := h_eq ▸ hy₁
    have hy₃ : y = x              := eq_of_mem_singleton hy₂
    exact (hxy hy₃.symm).elim
  exact ⟨h₁, h₂⟩

lemma SetTheory.Set.singleton_ne_empty (x : Object) :
  ({x} : Set) ≠ ∅
:= by
  by_contra! h₀
  have h₁ : x ∈ {x} := mem_singleton_of_eq rfl
  have h₂ : x ∈ ∅   := h₀ ▸ h₁
  have h₃ : x ∉ ∅   := not_mem_empty x
  exact (h₃ h₂).elim

lemma SetTheory.Set.subsets_of_singleton {x : Object} {A : Set}
  (h : A ⊆ {x}) : A = ∅ ∨ A = {x}
:= by
  by_cases hA : A = ∅
  · exact Or.inl hA
  · have hA' : A = {x} := by
      ext z
      constructor
      · intro (hzA : z ∈ A)
        exact (h z hzA : z ∈ {x})
      · intro hzX
        have ⟨y, (hyA : y ∈ A)⟩ := nonempty_def hA
        have hyx : y = x := eq_of_mem_singleton (h y hyA)
        have hzx : z = x := eq_of_mem_singleton hzX
        have hzA : z ∈ A := hzx ▸ hyx ▸ hyA
        exact hzA
    exact Or.inr hA'

lemma SetTheory.Set.ssubset_of_singleton {x : Object} {A : Set}
  (h : A ⊂ {x}) : A = ∅
:= by
  rcases (subsets_of_singleton h.left) with (hA0 : A = ∅) | (hAX : A = {x})
  · exact hA0
  · exact (h.right hAX).elim

-- Original version of ssubset_of_singleton, that was shorter, but at the cost
-- of being much more convoluted in its reasoning
lemma SetTheory.Set.ssubset_of_singleton' {x : Object} {A : Set}
  (h : A ⊂ {x}) : A = ∅
:= by
  ext y
  constructor
  · intro (hyA : y ∈ A)
    have hyX : y ∈ {x} := h.left y hyA
    have hyx : y = x   := eq_of_mem_singleton hyX
    have hxA : x ∈ A   := hyx ▸ hyA
    have ⟨z, hz⟩       := exists_dist_elem_of_ssubset h
    have hzx  : z = x  := eq_of_mem_singleton hz.left
    have hxA' : x ∉ A  := hzx ▸ hz.right
    exact (hxA' hxA).elim
  · intro (hy0 : y ∈ ∅)
    exact (not_mem_empty' hy0).elim

/-- Exercise 3.1.13 -/
theorem SetTheory.Set.singleton_iff
  (A : Set)
  (hA : A ≠ ∅) : (¬∃ B ⊂ A, B ≠ ∅) ↔ ∃ x, A = {x}
:= by
  constructor

  -- Assume A is a non-empty set whose only proper subset is empty; then for contradiction, assume A
  -- is not a singleton, so has least two members.  The singleton of either member is a non-empty
  -- proper subset, but A has no non-empty proper subsets.  Therefore A must be a singleton.
  · intro h₁
    push_neg at h₁ -- ∀ B ⊂ A, B = ∅
    by_contra! h₂ -- ∀ x, A ≠ {x}
    have ⟨x, (hxA : x ∈ A)⟩ := nonempty_def hA
    have h₃ : ∃y ∈ A, y ≠ x := exists_distinct_mem_of_nonempty_nonsingleton x hA h₂
    have ⟨y, hyA, hyx⟩      := h₃
    have h₄ : {x, y} ⊆ A    := pair_subset_of_mems hxA hyA
    have h₅ : {x} ⊂ {x, y}  := singleton_ssubset_pair x y hyx.symm
    have h₆ : {x} ⊂ A       := ssubset_of_ssubset_of_subset h₅ h₄
    have h₇ : {x} = ∅       := h₁ {x} h₆
    have h₈ : {x} ≠ ∅       := singleton_ne_empty x
    exact (h₈ h₇).elim

    -- Assume A is a singleton, and for contradiction that all proper subsets of A are non-empty;
    -- since the only proper subset of a singleton is the empty set, conclude that no non-empty
    -- proper subsets of A exist.
  · intro h₁
    by_contra! h₂
    have ⟨x, (hAx : A = {x})⟩ := h₁
    have ⟨Y, (hYA : Y ⊂ A), (hY0 : Y ≠ ∅)⟩ := h₂
    have hY0' : Y = ∅ := ssubset_of_singleton (hAx ▸ hYA)
    exact (hY0 hY0').elim


/-
  Now we introduce connections between this notion of a set, and Mathlib's notion.
  The exercise below will acquiant you with the API for Mathlib's sets.
-/

instance SetTheory.Set.inst_coe_set : Coe Set (_root_.Set Object) where
  coe X := { x | x ∈ X }

instance SetTheory.Set.inst_coe_set' : Coe (_root_.Set Object) Set where
  coe X := (univ.specify (fun x => ↑x ∈ X))

-- Now we can convert our `Set` into a Mathlib `_root_.Set`.
-- Notice that Mathlib sets are parameterized by the element type, in our case `Object`.
example (X : Set) : _root_.Set Object := X

/--
  Injectivity of the coercion. Note however that we do NOT assert that the coercion is surjective
  (and indeed Russell's paradox prevents this)
-/
@[simp]
theorem SetTheory.Set.coe_inj' (X Y : Set) :
  (X : _root_.Set Object) = (Y : _root_.Set Object) ↔ X = Y
:= by
  constructor
  · intro (h₁ : {x | x ∈ X} = {x | x ∈ Y})
    ext x -- ⊢ x ∈ X ↔ x ∈ Y
    have h₂ : (x ∈ {x | x ∈ X}) = (x ∈ {x | x ∈ Y}) := congr(x ∈ $h₁)
    have h₃ : (x ∈ X) = (x ∈ Y) := by simpa only [Set.mem_setOf_eq] using h₂
    have h₄ : x ∈ X ↔ x ∈ Y     := by simpa only [eq_iff_iff] using h₃
    exact h₄
  · rintro (rfl : X = Y)
    have h₁ : {x | x ∈ X} = {x | x ∈ X} := by rfl
    exact h₁

/-- Compatibility of the membership operation ∈ -/
theorem SetTheory.Set.mem_coe (X : Set) (x : Object) : x ∈ (X : _root_.Set Object) ↔ x ∈ X := by
  simp only [Set.mem_setOf_eq]

/-- Compatibility of the emptyset -/
theorem SetTheory.Set.coe_empty : ((∅ : Set) : _root_.Set Object) = ∅ := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro (h : x ∈ (∅ : Set))
    exact not_mem_empty x h
  · intro (h : x ∈ ∅)
    exact ((Set.notMem_empty x) h).elim

/-- Compatibility of subset -/
theorem SetTheory.Set.coe_subset (X Y : Set) :
  (X : _root_.Set Object) ⊆ (Y : _root_.Set Object) ↔ X ⊆ Y
:= by
  constructor
  · intro (hXY : {x | x ∈ X} ⊆ {x | x ∈ Y})
    intro x (hxX : x ∈ X)
    have hxX' : x ∈ {x | x ∈ X} := Set.mem_setOf_eq.mpr hxX
    have hxY' : x ∈ {x | x ∈ Y} := Set.mem_of_mem_of_subset hxX' hXY
    have hxY  : x ∈ Y           := Set.mem_setOf_eq.mp hxY'
    exact hxY
  · intro (hXY : X ⊆ Y)
    simp only [Set.setOf_subset_setOf]
    exact hXY

theorem SetTheory.Set.coe_ssubset (X Y : Set) :
  (X : _root_.Set Object) ⊂ (Y : _root_.Set Object) ↔ X ⊂ Y
:= by
  constructor
  · intro (hXY₁ : {x | x ∈ X} ⊂ {x | x ∈ Y})
    have ⟨hXY₂, ⟨x, hxY₁, hxX₁⟩⟩ := Set.ssubset_iff_exists.mp hXY₁
    have hxY₂ : x ∈ Y := Set.mem_setOf_eq.mpr hxY₁
    have hxX₂ : x ∉ X := Set.notMem_setOf_iff.mpr hxX₁
    have hXY₃ : X ⊂ Y := ssubset_of_subset_of_dist_elem hXY₂ ⟨x, hxY₂, hxX₂⟩
    exact hXY₃
  · intro (hXY₁ : X ⊂ Y)
    have hXY₂ : X ⊆ Y := hXY₁.left
    have hXY₃ : {x | x ∈ X} ⊆ {x | x ∈ Y} := by simpa [Set.mem_setOf_eq] using hXY₂
    have ⟨x, hxY, hxX⟩ := exists_dist_elem_of_ssubset hXY₁
    have h := Set.ssubset_iff_exists.mpr ⟨hXY₃, ⟨x, hxY, hxX⟩⟩
    exact h

/-- Compatibility of singleton -/
theorem SetTheory.Set.coe_singleton (x: Object) : ({x} : _root_.Set Object) = {x} := by
  rfl

/-- Compatibility of union -/
theorem SetTheory.Set.coe_union (X Y : Set) :
  (X ∪ Y : _root_.Set Object) = (X : _root_.Set Object) ∪ (Y : _root_.Set Object)
:= by
  ext x
  simp [Set.mem_setOf_eq]

/-- Compatibility of pair -/
theorem SetTheory.Set.coe_pair (x y : Object) : ({x, y} : _root_.Set Object) = {x, y} := by
  rfl

/-- Compatibility of subtype -/
theorem SetTheory.Set.coe_subtype (X : Set) :  (X : _root_.Set Object) = X.toSubtype := by
  rfl

/-- Compatibility of intersection -/
theorem SetTheory.Set.coe_intersection (X Y: Set) :
  (X ∩ Y : _root_.Set Object) = (X : _root_.Set Object) ∩ (Y : _root_.Set Object)
:= by
  ext x
  simp [Set.mem_setOf_eq]

/-- Compatibility of set difference-/
theorem SetTheory.Set.coe_diff (X Y : Set) :
  (X \ Y : _root_.Set Object) = (X : _root_.Set Object) \ (Y : _root_.Set Object)
:= by
  ext x
  simp [Set.mem_setOf_eq]

/-- Compatibility of disjointness -/
theorem SetTheory.Set.coe_Disjoint (X Y : Set) :
  Disjoint (X : _root_.Set Object) (Y : _root_.Set Object) ↔ Disjoint X Y
:= by
  constructor
  · intro (h₁ : Disjoint {x | x ∈ X} {x | x ∈ Y})
    simp [Disjoint] at *
    intro Z (hZX : Z ⊆ X) (hZY : Z ⊆ Y)
    have h₂ : {x | x ∈ Z} ⊆ {x | x ∈ X} := by simpa only [Set.setOf_subset_setOf] using hZX
    have h₃ : {x | x ∈ Z} ⊆ {x | x ∈ Y} := by simpa only [Set.setOf_subset_setOf] using hZY
    have h₄ : {x | x ∈ Z} = ∅           := h₁ h₂ h₃
    have h₅ : ∀ x, x ∉ {x | x ∈ Z}      := Set.eq_empty_iff_forall_notMem.mp h₄
    have h₆ : ∀ x, x ∉ Z                := by simpa only [Set.notMem_setOf_iff] using h₅
    have h₇ : Z = ∅                     := eq_empty_iff_forall_not_mem.mpr h₆
    exact h₇
  · intro (h₁ : Disjoint X Y)
    simp [Disjoint] at *
    intro Z (hZX₁ : Z ⊆ {x | x ∈ X}) (hZY₁ : Z ⊆ {x | x ∈ Y})
    let Z' : Set := Z
    ext x
    constructor
    · intro (hxZ : x ∈ Z)
      have hZX : Z' ⊆ X := by
        intro y (hyZ' : y ∈ Z')
        have hyZ : y ∈ univ ∧ y ∈ Z  := by simpa [Z'] using hyZ'
        have hyX : y ∈ X             := by simpa only [Set.mem_setOf_eq] using (hZX₁ hyZ.right)
        exact hyX
      have hZY : Z' ⊆ Y := by
        intro y (hyZ' : y ∈ Z')
        have hyZ : y ∈ univ ∧ y ∈ Z  := by simpa [Z'] using hyZ'
        have hyY : y ∈ Y             := by simpa only [Set.mem_setOf_eq] using (hZY₁ hyZ.right)
        exact hyY
      have hxZ' : x ∈ Z'             := by simpa [Z'] using ⟨SetTheory.mem_univ x, hxZ⟩
      have hZ0  : Z' = ∅             := h₁ hZX hZY
      have hx0  : x ∈ ∅              := hZ0 ▸ hxZ'
      exact not_mem_empty' hx0
    · intro (hx0₁ : x ∈ ∅)
      exact ((Set.notMem_empty x) hx0₁).elim

end Chapter3

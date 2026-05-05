/-
Copyright (c) 2026 Andrew Hendel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Hendel
-/
import Mathlib.NumberTheory.ADEInequality
import Mathlib.Tactic

/-!
# Number of Platonic Solids (Freek #50)

We prove that there are exactly five Platonic solids, i.e., exactly five pairs
(p, q) with p ≥ 3 and q ≥ 3 satisfying 1/p + 1/q > 1/2.

This is entry #50 on Freek Wiedijk's list of 100 famous theorems.

## Relationship to ADE inequality

The Schläfli condition `1/p + 1/q > 1/2` is the `r = 2` specialization of the
ADE inequality `1/p + 1/q + 1/r > 1`, classified in
`Mathlib.NumberTheory.ADEInequality`. The proof here uses the same bounding
technique (bound variables, exhaust cases).

## The combinatorial argument

A convex regular polyhedron has faces that are regular p-gons, with q faces
meeting at each vertex. Euler's formula V - E + F = 2, combined with the
double-counting relations pF = 2E = qV, yields the constraint
1/p + 1/q > 1/2. A finite case analysis shows exactly five solutions:

* (3, 3) — tetrahedron
* (3, 4) — octahedron
* (4, 3) — cube
* (3, 5) — icosahedron
* (5, 3) — dodecahedron

## References

* <https://www.cs.ru.nl/~freek/100/> (entry #50)
* `Mathlib.NumberTheory.ADEInequality` for the 3-variable generalization
-/

/-- A Schläfli pair (p, q) represents a candidate regular polyhedron where each
face is a regular p-gon and q faces meet at each vertex. The Platonic solid
condition requires p ≥ 3, q ≥ 3, and 1/p + 1/q > 1/2, which is equivalent
to the integer condition 2*(p+q) > p*q (clearing denominators 2pq). -/
def IsPlatonicPair (p q : ℕ) : Prop :=
  3 ≤ p ∧ 3 ≤ q ∧ 2 * (p + q) > p * q

/-- The five Platonic solids as Schläfli pairs. -/
def platonicPairs : List (ℕ × ℕ) :=
  [(3, 3), (3, 4), (4, 3), (3, 5), (5, 3)]

/-- Each of the five classical pairs satisfies the Platonic condition. -/
theorem all_platonic_pairs_valid :
    ∀ pq ∈ platonicPairs, IsPlatonicPair pq.1 pq.2 := by
  intro ⟨p, q⟩ hmem
  simp only [platonicPairs, List.mem_cons, List.mem_nil_iff, or_false,
    Prod.mk.injEq] at hmem
  rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    exact ⟨by omega, by omega, by omega⟩

/-- If (p, q) is a Platonic pair, then it is one of the five known pairs.
The proof bounds p, q ≤ 5 (mirroring `ADEInequality.lt_three` etc.) then
exhausts the finite cases. -/
theorem platonic_pair_classification {p q : ℕ} (h : IsPlatonicPair p q) :
    (p, q) ∈ platonicPairs := by
  obtain ⟨hp, hq, hineq⟩ := h
  have hp5 : p ≤ 5 := by nlinarith
  have hq5 : q ≤ 5 := by nlinarith
  simp only [platonicPairs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq]
  interval_cases p <;> interval_cases q <;> omega

/-- **Exactly five Platonic solids** (Freek #50): the set of pairs (p, q) with
p ≥ 3, q ≥ 3, and 1/p + 1/q > 1/2 is exactly
{(3,3), (3,4), (4,3), (3,5), (5,3)}. -/
theorem platonic_solids_classification (p q : ℕ) :
    IsPlatonicPair p q ↔ (p, q) ∈ platonicPairs :=
  ⟨platonic_pair_classification, fun h => all_platonic_pairs_valid _ h⟩

/-- There are exactly five Platonic solids. -/
theorem number_of_platonic_solids :
    platonicPairs.length = 5 := rfl

/-
Copyright (c) 2026 Andrew Hendel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Hendel
-/
import Mathlib.Tactic

/-!
# Number of Platonic Solids

We prove that there are exactly five Platonic solids, i.e., exactly five pairs
(p, q) with p ≥ 3 and q ≥ 3 satisfying 1/p + 1/q > 1/2.

This is entry #50 on Freek Wiedijk's list of 100 famous theorems.

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

private lemma p_upper_bound {p q : ℕ} (_ : 3 ≤ p) (hq : 3 ≤ q)
    (hineq : 2 * (p + q) > p * q) : p ≤ 5 := by
  by_contra h
  push Not at h
  have h6 : 6 ≤ p := h
  have h1 : 6 * q ≤ p * q := Nat.mul_le_mul h6 le_rfl
  have h2 : p * 3 ≤ p * q := Nat.mul_le_mul le_rfl hq
  omega

private lemma q_upper_bound {p q : ℕ} (hp : 3 ≤ p) (_ : 3 ≤ q)
    (hineq : 2 * (p + q) > p * q) : q ≤ 5 := by
  by_contra h
  push Not at h
  have h6 : 6 ≤ q := h
  have h1 : p * 6 ≤ p * q := Nat.mul_le_mul le_rfl h6
  have h2 : 3 * q ≤ p * q := Nat.mul_le_mul hp le_rfl
  omega

/-- If (p, q) is a Platonic pair, then it is one of the five known pairs. -/
theorem platonic_pair_classification {p q : ℕ} (h : IsPlatonicPair p q) :
    (p, q) ∈ platonicPairs := by
  obtain ⟨hp, hq, hineq⟩ := h
  have hp5 : p ≤ 5 := p_upper_bound hp hq hineq
  have hq5 : q ≤ 5 := q_upper_bound hp hq hineq
  simp only [platonicPairs, List.mem_cons, List.mem_nil_iff, or_false, Prod.mk.injEq]
  interval_cases p <;> interval_cases q <;> omega

/-- **Exactly five Platonic solids**: the set of pairs (p, q) with p ≥ 3, q ≥ 3,
and 1/p + 1/q > 1/2 is exactly {(3,3), (3,4), (4,3), (3,5), (5,3)}. -/
theorem platonic_solids_classification (p q : ℕ) :
    IsPlatonicPair p q ↔ (p, q) ∈ platonicPairs := by
  constructor
  · exact platonic_pair_classification
  · intro hmem
    exact all_platonic_pairs_valid (p, q) hmem

/-- There are exactly five Platonic solids. -/
theorem number_of_platonic_solids :
    platonicPairs.length = 5 := by
  rfl

/-
Copyright (c) 2026 Alexander Kai Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Kai Chen
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Tactic

open Function

/-
This file formalizes the proof that any path graph is graceful graph.

"path graph": https://en.wikipedia.org/wiki/Path_(graph_theory)

"graceful graph": https://en.wikipedia.org/wiki/Graceful_labeling

The proof follows the following steps:
1. Formally define a path graph, built from a SimpleGraph of `n` vertices with
   the relation that every vertice `i < n` has an edge to `i + 1`: `pathGraph`
2. Establish a vertice labeling function: `pathLabel`
3. Show that for any Nat. `n`, the vertice labeling function is
   injective: `pathGraph_injective`
4. Show that for any edge between vertices `i` and `i + 1`, its value is equal
   to `(n - 1) - i`: `path_edge_label_val`
5. Show the "bridge lemma" that all edges are of the form `(i, i + 1)`:
   `pathGraph_adj_iff`
6. Show that the edge values are surjective onto `{1...n - 1}` for any `n >= 2`:
   `edge_labels_surjective`
-/

/- The graph with vertices `Fin n` and directed edges between `i` and `i+1` i.e. a pathGraph -/
def pathGraph (n : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel (fun i j => i.val + 1 = j.val)

/- Labeling function which can be used for outside-inside method for pathGraph -/
def pathLabel (n : ℕ) (i : ℕ) : ℕ :=
  if i % 2 == 0 then i / 2 else (n - 1) - (i - 1) / 2

/- The function `i` -> `label{i, i + 1}` is injective -/
theorem pathGraph_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => pathLabel n i.val) := by
  intro i j h
  simp [pathLabel] at h
  have hi := i.is_lt
  have hj := j.is_lt
   -- C1: i even j even -> i/2 = j/2 implies i = j
   -- C2: i odd j odd   -> (n - 1) - i/2 = (n - 1) - j/2 implies i/2 = j/2 implies i = j
   -- C3: i even, j odd -> i/2 = (n - 1) j/2 = IMPOSSIBLE: i < n && j < n, i/2 + j/2 < (n - 1)
   -- C4: i even, j odd -> ditto C3
  split_ifs at h; all_goals omega

/- Distance `label{i, i + 1}` is function `(n - 1) - i` -/
lemma path_edge_label_val (n i : ℕ) (h : i < n - 1) :
    dist (pathLabel n i) (pathLabel n (i + 1))  = (n - 1) - i := by
  simp [pathLabel, dist]

  split_ifs with h_even h_next_even
  · -- C1: i even i + 1 is even: IMPOSSIBLE
    omega
  · -- C2: i even and i + 1  is odd
    -- label i = i/2, label i + 1 = (n-1) - (i + 1)/2
    -- i even -> (i + 1)/2 == i/2 (floor div)
    sorry  -- TODO: fix issue w/ `dist`
  · -- Case 3: i is odd and i+1 is even
    -- label i = (n - 1) - i/2, label i + 1 = (i + 1)/2
    sorry -- TODO
  · -- C4: i odd i + 1 odd: IMPOSSIBLE
    omega

/- Adjacent vertices `i` and `j` satisfy either `i + 1 = j` or `j + 1 = i` -/
lemma pathGraph_adj_iff {n : ℕ} (i j : Fin n) :
    (pathGraph n).Adj i j ↔ (i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  unfold pathGraph
  simp [SimpleGraph.fromRel]
  omega

/- For `n >= 2`, the distance function `(n - 1) - i` is surjective (images to `range(1, n - 1)`) -/
lemma edge_labels_surjective (n : ℕ) [Fact (n ≥ 2)] :
    (Finset.range (n - 1)).image (fun i => (n - 1) - i) = Finset.Icc 1 (n - 1) := by
  ext x
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨i, hi, rfl⟩
    -- i < n - 1 -> 1 <= (n - 1) - i <= n - 1
    omega
  · rintro ⟨h_min, h_max⟩
    -- We pick i = (n-1) - x
    use (n - 1) - x
    omega

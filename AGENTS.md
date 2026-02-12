After finishing updating the Lean code, verify it by running `lake build`.

For a chain of implications explicitly referred by words "implication tuple" in informal theorem condition (1)->(2)->...->(n) create a namespace with implications:
(1)->(2), (2)->(3), ..., (n-1)->(n)
and as their consequences (1)->(n), (2)->(n), ..., (n-2)->(n).
Use keyword `lemma` for (1)->(2), (2)->(3), ..., (n-2)->(n-1), because these implications are meant only to prove theorems:
(1)->(n), (2)->(n), ..., (n-1)->(n).
Export these theorems from the namespace.
Name the namespace accordingly the statement semantic name, not like Tuple572 or Theorem572.

In uploaded images or LaTeX fragments accept unusual set notation like
$\left\{\frac{x\in A}{P(x)}\right\}$.
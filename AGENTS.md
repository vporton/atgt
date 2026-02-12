For an implication chain (1)->(2)->...->(n) create a namespace with implications:
(1)->(2), (2)->(3), ..., (n-1)->(n)
and as their consequences (1)->(n), (2)->(n), ..., (n-2)->(n).
Use keyword `lemma` for (1)->(2), (2)->(3), ..., (n-2)->(n-1), because these implications are meant only to prove theorems:
(1)->(n), (2)->(n), ..., (n-1)->(n).
Export these theorems from the namespace.
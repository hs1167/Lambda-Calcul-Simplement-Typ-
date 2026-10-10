# STLC

typed extension of [Mumei](https://github.com/hs1167/Mumei): same De Bruijn / shift / substitution / CBV machinery, now with a static layer.

```math
\Gamma \vdash t : T
```

syntax-directed typing makes the typechecker almost literally the inversion lemma made executable: inspect the shape of \(t\), recover the constraints imposed by its typing rule, reject if they cannot be satisfied.

nice separation to keep in mind:

```math
\text{static semantics: } \Gamma \vdash t:T
\qquad\qquad
\text{dynamic semantics: } t \to t'
```

typecheck once before evaluation; progress + preservation are the metatheoretic reason this is enough.

semantics and typing rules follow Pierce, *Types and Programming Languages*.

todo: go much deeper on what types actually are via Curry Howard, dependent types, eventually categorical semantics; implementing a typechecker is not yet a license to see categories everywhere hehe
todo: rebuild STLC cleanly in Rocq and mechanize as much of its metatheory as possible: weakening, substitution, progress, preservation, etc.

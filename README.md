# Synthetic Tait Computability in Agda

The main difficulty with formalising synthetic Tait computability is how to
represent the open proposition (for which I will write `#`). Presentations of
STC usually use extensional equality, thus omitting many steps of reasoning
about how things collapse under `#`.

There are two known approaches to formalising STC:

- Postulating a proposition `#` directly. This basically leads to rewriting
  hell, even with `--prop`. Rewriting rules don't help because we cannot rewrite
  a term based on the existence of an element `p : #` in the ambient context,
  which is not otherwise referenced in the term.
- Postulating a cofibration `#` in cubical mode. Then at least glue and
  extension types can be formulated using cubical primitives. However it is
  pretty hacky and Agda's cofibrations do not really behave properly (they
  emulate the internal language of a de Morgan topos, and none of the usual STC
  examples fall under this AFAIK).
  
Ideally we would want an implementation of type theory with propositions (like
in [Andreas Nuyts' PhD thesis](https://lirias.kuleuven.be/retrieve/581985), also
suggested in https://github.com/agda/agda/issues/7703).

However, it turns out that if we explicitly separate the `#-modal` part and the
`#-contractible` part of each object, then it is pretty easy to get good
definitional behaviour. Specifically, we work in an indexed type theory, which has:

- base sorts `Tyᵇ : Set` , `Tmᵇ : Tyᵇ → Set`
- indexed sorts `Tyᶠ : Tyᵇ → Set` , `Tmᶠ : ∀ {Aᵇ} → Tyᶠ Aᵇ → Tmᵇ Aᵇ → Set`

The base universe is the universe of `#-modal` (open modal) types, and the
indexed universe is the (`#-contractible` / closed modal) universe of types lying
over a chosen base point.

In other words, you can think of
- `Aᵇ : Tyᵇ` as `Aᵇ : ○ U`
- `Aᶠ : Tyᶠ Aᵇ` as `Aᶠ : { U | # ↪ Aᵇ } `

(Strict) closed-modal types are those which are indexed over the unit type: `Tyᶠ
𝟙ᵇ`.

We do not have access to `#` directly, but we can postulate glue and extension
types. These have a rather neat formulation:
```
Glue : (Tmᵇ Aᵇ → Tyᶠ 𝟙ᵇ) ≃ Tyᶠ Aᵇ : Ext
```
up to term isomorphism. This means that Glue takes a base-indexed family
of closed-modal types and produces a 'total' type, while Ext takes a total type
and a base point and produces a closed-modal type.

We can also add the closed modality (`● : Tyᶠ Aᵇ → Tyᶠ 𝟙ᵇ`) and open immersion
(`○ : (Aᵇ : Tyᵇ) → Tyᶠ Aᵇ`) with appropriate intro/elim rules. The open modality
is just projection of the index `Aᵇ`. See `LF.agda`.

This is all we need to define STC models. See `STLC.agda` for an example of
canonicity for the simply-typed lambda calculus.

There are still some disadvantages:
- It is not so nice to work with custom universes in Agda as it is to work with
  Set. In particular, we cannot use records or inductive types (though functions
  work pretty well with `syntax` sugar). For example, if we want to use records,
  we need to separately define a record for the base and one for the fibers.
  Alternatively we can work fully within the fibers if we stick to the postulated type
  formers, and the base will be 'computed' by Agda in the index.
- The setup is quite rigid to a single syntactic open. If we want more general
  setups with `n` syntactic opens (for example `n=2` for parametricity) we need a
  new logical framework that has `n` base universes, and the fibers indexed over
  all of them.


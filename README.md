# Synthetic Tait Computability in Agda

[Synthetic Tait
computability](https://kilthub.cmu.edu/articles/thesis/First_Steps_in_Synthetic_Tait_Computability_The_Objective_Metatheory_of_Cubical_Type_Theory/19632681?file=34869399) (STC)
is a [synthetic](https://en.wikipedia.org/wiki/Synthetic_mathematics) approach
to logical relations for type theories.

If you are looking for an accessible introduction to synthetic logical relations
via STC, check
[this](https://www.jonmsterling.com/bafkrmialyvkzh6w6snnzr3k4h2b62bztsk4le57idughqik24bltinieki.pdf)
out.

Now that you have read that, I assume you know the basics of STC and want to
learn about how we can mechanise it in Agda.

To recap, the main idea of STC is:

> Instead of manually building a first-order displayed model of type theory valued in a glued
> category, let's work in the internal language of this glued category, and
> build a _higher-order_ displayed model in it.

The main affordance of this approach is that we avoid dealing with the
substitution calculus altogether, cutting out most of the transport noise that
comes up in type-theoretic gluing.[^1] We can externalise the construction
only in the end, to extract the theorems we care about.

[^1]: For an example of this transport noise see Szumi Xie's impressive
    [formalisation of canonicity for MLTT](https://github.com/szumixie/mltt/blob/main/MLTT/Canonicity/Model.agda).

### Tradeoffs and alternatives

There are tradeoffs to using STC:

- As is the case for most synthetic mathematics, we are no longer working in
  'honest Set land', and must be okay with having some postulates and
  supplementing our formalisation with some external reasoning at the edges.
  
- There is no good notion of morphism of second or higher-order models that we
  can directly use internally. We have to build a new topos each time we want to
  work with such a morphism. As a result, we do not automatically get access to
  an internal induction principle with STC. Taichi Uemura [shows how to achieve
  this](https://arxiv.org/pdf/2212.11764) with enough gluing.
  
- It does not work for every logical relations setup. In particular, it
  only works when the glued category is (or can be made into) a Grothendieck topos.
  
- It can involve some rather [powerful semantic results](https://arxiv.org/abs/2202.12012) for more exotic setups.
  (Though, it is constructive for most common examples like canonicity/normalisation!)

There is also the 
[internal sconing](https://drops.dagstuhl.de/storage/00lipics/lipics-vol260-fscd2023/LIPIcs.FSCD.2023.18/LIPIcs.FSCD.2023.18.pdf)
approach of Bocquet. This is interesting because it provides access to an
induction principle directly. However, it is still not as nice to formalise as
STC, because the displayed models involved are over *first-order* models, so we
still need to deal with the substitution calculus.

### Why is it hard to mechanise STC?

Up until now, formalising synthetic Tait computability has also been mostly out
of reach, because the STC way of building displayed models is through synthetic
phase distinctions. Recall that the internal language of a glued topos contains
two lex modalities `○` and `●`, defined as `ϕ → -` (exponentiation) and `ϕ * -`
(join) for an abstract proposition `ϕ`. When we build a model of a type theory
`T` inside such a glued topos, this is automatically a displayed model, in the
sense that the projection to the base is given by introducing a witness of `ϕ`
into scope, and the fibers of this projection are the 'displayed' data.

The issue is that the computation of this base does not happen definitionally
when we are under `ϕ`---it only happens propositionally. This reintroduces so
much transport noise that it basically becomes just as difficult as the vanilla
first-order gluing approach. The reason this works on paper is that we work in
extensional type theory, so we have various definitional equations that hold if
there is a `ϕ` somewhere in scope. In intensional type theory this is not
possible, and we cannot even hack Agda with rewriting rules to achieve this.

One way around this is is to work in Cubical Agda and postulate a cofibration
`ϕ` in cubical mode (e.g. https://github.com/jonsterling/agda-stc). Then we take
advantage of the fact that Cubical Agda has glue types to emulate this
definitional collapsing behaviour. However, this is not sound for many reasons,
one of which is that cofibrations do not behave as propositions in a glued topos
should.

## A structured approach to internal gluing

This library is based on the observation that each type in a glued topos is
equivalent to a `○`-modal base and a `●`-modal family over it. In particular,
given a universe `U`, we have:

```hs
U ≅ (A : U○) × (A → U●)
```

where `U○` and `U●` are the open- and closed-modal subuniverses of `U`
respectively.

This is commonly called a 'fracture' theorem. Because this is the case, we can
work inside a fractured universe from the beginning, so that the base and fibers
are always structurally separated, rather than trying to prove this fracture
theorem internally after the fact.

As such, in this library, we work inside an _indexed type theory_. This is a
type theory which has base types, fiber types, base terms and fiber terms. At
each level (base, fiber) we have type formers. We specify this as a SOGAT.

The sorts are:

```hs
-- Base
Setᵇ : 𝒰
Elᵇ : Setᵇ → 𝒰⁺

-- Fiber
Setᶠ : Setᵇ → 𝒰
Elᶠ : ∀ Aᵇ . Setᶠ Aᵇ → Elᵇ Aᵇ → 𝒰⁺
```

The base is just ordinary dependent type theory, nothing too interesting to see
here:

```hs
-- Unit types
𝟙 : Setᵇ
(ttᵇ, ttᵇ-uniq) : isContr (Elᵇ 𝟙)

-- Pi
Πᵇ : (Aᵇ : Setᵇ) → (Elᵇ Aᵇ → Setᵇ) → Setᵇ
(lamᵇ, appᵇ) : ((x : Elᵇ Aᵇ) → Elᵇ (Bᵇ x)) ≅ Elᵇ (Πᵇ Aᵇ Bᵇ)

-- Sigma, etc..
```


It is in the fibers that we get all the interesting type formers.


### Glue types

The `Glue` type former take a base type `Aᵇ`, and a family of fiber types `Bᶠ`
over the unit `𝟙ᵇ` (so, a closed modal family), and produces a fiber type over
`Aᵇ`:

```hs
Glue : (Aᵇ : Setᵇ) → (Elᵇ Aᵇ → Setᶠ 𝟙) → Setᶠ Aᵇ
(glue, unglue) : Elᶠ (Bᶠ aᵇ) ttᵇ ≅ Elᶠ (Glue Aᵇ Bᶠ) aᵇ
```

Glue types allow us to artificially place any fiber data over any base data,
which is the first main way we construct interesting things. In a logical
relations model, most sorts and operations will be interpreted by gluing the
corresponding base sort/constructor with whatever computability data we want to
carry in the fibers.

### Extension types

The `Ext` type former is in a sense the dual of `Glue`. It takes a fiber type
`Aᶠ` over `Aᵇ`, as well as a base element `aᵇ` of `Aᵇ`, and produces a type over
the unit `𝟙ᵇ` that 'remembers' the chosen base point `aᵇ`:

```hs
Ext : Setᶠ Aᵇ → Elᵇ Aᵇ → Setᶠ 𝟙 
(ext, unext) : Elᶠ Aᶠ aᵇ ≅ Elᶠ (Ext Aᵇ aᵇ) ttᵇ
```

Extension types allow us to internalise the concept of a 'single fiber' and
treat it as pure computability data (closed-modal). This is the second main way
we construct interesting things; the data we carry in the fibers of a glued
object will often be made of extension types.

In what sense are they dual to glue types? `Ext` and `Glue` form an
isomorphism-up-to-isomorphism between fiber types, and families of closed-modal
types over base elements:

```hs
Ext : Setᶠ Aᵇ ≃ (Elᵇ Aᵇ → Setᶠ 𝟙ᵇ) : Glue
```

This is already a fiberwise kind of fracture theorem.


### Open modality

One thing we could call an 'open modality' in this setup is basically a
fiberwise unit type:

```hs
○ : (Aᵇ : Setᵇ) → Setᶠ Aᵇ
(η○ , η○-uniq) : ∀ aᵇ . isContr (Elᶠ (○ Aᵇ) aᵇ)
```

This gives a copy of the base theory inside the fiber theory, which we use in
logical relations to specify conditions on the base model as part of some
computability data.

### Closed modality

The closed modality is the least pleasant to use because it is a positive type,
i.e. it does not come in the form of a definitional isomorphism:

```hs
● : Setᶠ Aᵇ → Setᶠ 𝟙ᵇ

η● : Elᶠ Aᶠ aᵇ → Elᶠ (● Aᶠ) ttᵇ

elim● : (P : Elᶠ (● Aᶠ) ttᵇ → Setᶠ 𝟙ᵇ)
  → (η●ᴹ : ∀ aᵇ . (aᶠ : Elᶠ Aᶠ aᵇ) → Elᶠ (Pᶠ (η● aᶠ)) ttᵇ)
  → ∀ aᶠ → Elᶠ (Pᶠ aᶠ) ttᵇ
  
elim-●-η● : elim-● Pᶠ η●ᴹ (η● aᶠ) ≡ η●ᴹ aᶠ
```

The elimination principle says that we can treat a `● Aᶠ` as an `Aᶠ` as long as
we produce something that is closed modal, i.e. indexed by `𝟙ᵇ`. From this we
can see that `●` is a monad as usual. At least it is more pleasant to use than
the usual QIT definition in STC, because we automatically get the 'contractible
under `ϕ`' behaviour by the fact that it is indexed by `𝟙ᵇ`.

This is also important for logical relations, because it allows us to take any
'mixed' type and erase the base, treating it as pure computability data.
(Do not confuse with extension types, which remember the base!) However, we could
avoid many uses of this if we natively close `Setᶠ 𝟙ᵇ` under enough type formers.


## Other useful references


["Homotopy type theory as internal languages of
diagrams of ∞-logoses" by Taichi Uemura](https://arxiv.org/pdf/2212.02444v1)

- Useful to get a better idea of how synthetic phases correspond to gluing of toposes.

["Modalities in homotopy type theory" by Egbert Rijke, Michael Shulman, Bas
Spitters](https://arxiv.org/pdf/1706.07526)

- The de-facto reference on lex modalities




<!-- 
## Formalising STC

The main difficulty with formalising synthetic Tait computability is how to
represent the open proposition for which I will write `#`). Presentations of
STC usually use extensional equality, thus omitting many steps of reasoning
about how things collapse under `#`.

There are two known approaches to formalising STC:

- Postulating a proposition `#` directly, and postulate the realignment axiom. This basically leads to transport
  hell, even with `--prop`. Rewriting rules don't help because we cannot rewrite
  a term based on the existence of an element `p : #` in the ambient context,
  which is not otherwise referenced in the term.
- Postulating a cofibration `#` in cubical mode (e.g. https://github.com/jonsterling/agda-stc).
  Then at least glue and extension types can be formulated using cubical primitives.
  However it is pretty hacky and Agda's cofibrations do not really behave properly (they
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
 -->



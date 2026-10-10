# 2.1 Kinds and Types

Since `Core` is a typed λ-calculus, the story naturally begins by introducing **types** in Core.
What makes the theory somewhat intricate is that its four main components—types, kinds, rows, and
effects—are mutually recursive; each is defined in terms of the other three.
Therefore, whichever component we choose to begin with, we inevitably must mention concepts that
have not yet been introduced.

As a first approximation, types are classifier for terms. What sets `Core` apart from the textbook
simply typed λ-calculus (STLC) is that its types are **higher-kinded**. That is, `Core` features a
variety of type-level entities, and **kinds** are what classify these entities.

- `Type` is the most fundamental kind: it is the kind of types to which every `Core` term belongs.
- **Type constructors**, namely *type-indexed types* like `Array`, have the kind `Type -> Type`.
  This means that given a type of kind `Type` (e.g., `Int`), the constructor yields a new type
  (e.g., `Array Int`).
- `Row κ` is a keyed set of `κ`-kinded elements, which is described in depth in a later section.
- `Effect` is another fundamental kind that describes the types of effects. In Stella, the function
  arrow `T1 -> T2 / ρ` consists of three parts: the argument type `T1`, the return type `T2`, and
  `ρ` ― the set of effects that calling the function may yield. Hence, the arrow `->` has the kind
  `Type -> Row Effect -> Type -> Type`.

### 2.1.1 The Kind Syntax

The syntax for kinds is given as the following BNF grammar of three layers with a supplemental
element category:

```text
ε ::=                 -- the element kind
    | Type            -- the kind to which every Core term belongs
    | Effect          -- the kind to which every effect belongs
  
q ::=                 -- The quantifiable kinds
    | k               -- kind variable
    | Type            -- same as above
    | Row ε           -- the row kind
    | q1 -> q2        where result(q2) = Type

φ ::=                 -- effect-producing kinds
    | Effect          -- same as above
    | q -> φ          -- kind of effect constructors

κ ::=                 -- kinds
    | q
    | φ
```

There are a few points worth mentioning:

First, we have only two atomic kinds: `Type` and `Effect`. This is the restriction of our kind
system: In Stella, we cannot extend the set of atomic kinds by user-defined atomic kinds as
we could do in Haskell or PureScript.

Second, the `q1 -> q2` grammar is noted with the side-condition `result(q2) = Type`, where
result is structurally defined as:

- `result( κ1 -> κ2 )`  = `result( κ2 )`
- `result( κ )         = κ                 otherwise`

The argument to `Row` being `ε`, not a general `κ`, implies that we can have only two forms
of row kinds: `Row Type` and `Row Effect`.

Third, there is no ∀-quantified kind like `forall k̄. κ`. This is intentional ― in Stella,
kind variables can actually be quantified, namely we can have kind-polymorphic type constructors;
for instance,

```stella
data Proxy :: forall k. k -> Type
data Proxy a = Proxy
```

is a valid construction. In this declaration, `Proxy` has the kind `forall k. k -> Type`.
We call such a `forall`-quantified kind a **kind scheme** and distinguish them from kinds.

The syntax for kind schemes is given as:

```plain
Ψ ::=                  -- kind schemes
    | forall k̄. q      where result(q) = Type
```

This grammar immediately implies that every kind scheme has a prenex form (i.e., rank-1
polymorphic), namely all bound kind variables must be placed in the head of the kind scheme.
Therefore, while kinds like `forall k. k -> Type`, `forall k1 k2. k1 -> k2 -> Type`, ...
are all valid, kinds like `forall k1. k1 -> (forall k2. k2 -> Type) -> Type` are not.

Finally, kind equality is structural. A kind contains no binder of its own.
Kind schemes are identified up to α-equivalence of their prenex kind-variable binders.

> *Note*: There is no computation inside kinds: Stella has neither kind abstraction nor
> first-class kind application. Be careful not to confuse the notation `T [[κ̄]]` with
> an application of a kind-level function; this is the instantiation of the kind scheme of
> T, which will be introduced in the later section *The Syntax for Types*.

### 2.1.2 Judgement on Kind

In Core semantics, we have three judgements on kinds: **well-formedness, Effect-producing, and quantifiability**:

```plain
--  Judgement          Read as     
    Δ ⊢ κ qkind     -- κ is a quantifiable kind
    Δ ⊢ κ ekind     -- κ is an effect-producing kind
    Δ ⊢ κ kind      -- κ is a well-formed kind
```

Here, `Δ` is a **kind variable context** which is defined as:

```plain
Δ ::=                         -- a kind context
    | ・                      -- an empty kind variable context
    | Δ'; k   where k ∉ Δ'    -- extension with fresh kind-variable
```

**Kind quantifiability** judgement is given by the following rules:

```plain
    k ∈ Δ
------------- KQ-Var
  Δ ⊢ k qkind


---------------- KQ-Type
  Δ ⊢ Type qkind


---------------------- KQ-TypRow      ------------------------ KQ-EffRow
  Δ ⊢ (Row Type) qkind                 Δ ⊢ (Row Effect) qkind


  Δ ⊢ q1 qkind    Δ ⊢ q2 qkind    result(q2) = Type
--------------------------------------------------- KQ-Arrow
                  Δ ⊢ q1 -> q2 qkind
```

We can construct `∀`-quantified types only over type variables whose kinds are quantifiable, so while types like

```plain
∀ (a : Type). τ1
∀ (a : Type -> Type). τ2
∀ (ρ : Row Effect). τ3　
∀ (a : Row (Type -> Type)). τ4
```

are all valid, types such as

```plain
∀ (e : Effect). τ
∀ (e : Type -> Effect)
```

are not.

**Effect-producing** judgement is given by the following rules:

```plain
----------------- KE-Effect
Δ ⊢ Effect ekind

Δ ⊢ q qkind    Δ ⊢ φ ekind
-------------------------- KE-Arrow
Δ ⊢ q -> φ ekind
```

Finally, **Kind Well-formedness** is given by:

```plain
Δ ⊢ q qkind
──────────── KW-QKind
Δ ⊢ q kind


Δ ⊢ φ ekind
──────────── KW-EffKind
Δ ⊢ φ kind
```

With these rules, we can derive the following conclusion:

|Kind|Judgement|Reason|
|----|---------------|------|
|`Type`|Well-formed|KW-QKind, since `Type` is quantifiable (KQ-Type)  |
|`Row Type`|Well-formed|KW-QKind, since `Row Type` is quantifiable (KQ-TypRow) |
|`Type -> Type`|Well-formed|`Type` is quantifiable and `result(Type) = Type`, so `Type -> Type` is also quantifibale (KQ-Arrow)|
|`(Type -> Type) -> Type`|Well-formed|Similarly to the above (Use KQ-Arrow twice then KW-QKind)|
|`Effect`|Effect-producing, but not well-formed|`Effect` is effect-producing (KE-Effect), but not quantifiable|
|`Type -> Effect`|Effect-producing, but not well-formed|Since `Type` is quantifiable we can use KE-Arrow|
|`Row Type -> Effect`|Effect-Producing, but not Well-formed|Similarly to the above (again, `Row Type` is quantifiable)|
|`Effect -> Effect`|Invalid|`Effect` is not quantifiable, so precondition of KQ-Arrow does not hold|
|`(Type -> Effect) -> Type`|Inalid|Again, `Type -> Effect` is not quantifiable|
|`Type -> Row Type`|Invalid|Since `result(Row Type) ≠ Type` precondition of KQ-Arrow does not hold|

## 2.1.3 Well-formedness of Kind Scheme

Kind scheme's well-formedness is given by the following rules:

```plain
k̄ are pairwise distinct
k̄ ⊢ q qkind
result(q) = Type
──────────────────────────── KS-Form
⊢ forall k̄. q kscheme
```

Here, the precondition `result(q) = Type` comes from the fact that in Stella kind scheme is for type constructors.
Thus, while the following kind scheme is valid:

```plain
forall k. k -> Type
forall k1 k2. k1 -> k2 -> Type
forall k. (k -> Type) -> Type
```

the following are not:

```
forall k. k
forall k. k -> Row Type
forall k. k -> Effect
```

## 2.1.3 Types


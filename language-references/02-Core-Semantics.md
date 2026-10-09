# Chapter 2: The Core Semantics

In this chapter, we describe the core syntax and semantics of the language.
Ultimately, Stella is a series of syntax sugars over the `Core`, a small
functional system of typing and reduction rules based on a sort of *enriched*
System-F (a.k.a. second-order λ-calculus). The enrichment consists of
higher-kinded types, row and effect polymorphism. As a Stella professional,
it is indispensable to understand the `Core` semantics thoroughly!

## 2.1 Kinds and Types

Since `Core` is a typed λ-calculus, the story naturally begins by introducing **types** in Core.
What makes the theory somewhat intricate is that its four main components—types, kinds, rows, and
effects—are mutually recursive; each is defined in terms of the other three.
Therefore, whichever component we choose to begin with, we inevitably must mention concepts that
have not yet been introduced.

As a first approximation, types classify terms. What sets `Core` apart from the textbook simply
typed λ-calculus (STLC) is that its types are **higher-kinded**. That is, `Core` features a
variety of type-level entities, and **kinds** are what classify these entities.

- `Type` is the most fundamental kind: it is the kind of types to which every `Core` term belongs.
- **Type constructors**, namely *type-indexed types* like `Array`, have the kind `Type -> Type`.
  This means that given a type of kind `Type` (e.g., `Int`), the constructor yields a new type
  (e.g., `Array Int`).
- `Row κ` is a keyed set of elements of kind `κ`, which is described in depth in a later section.
- `Effect` is another fundamental kind that describes the types of effects. In Stella, the function
  arrow `T1 -> T2 / ρ` consists of three parts: the argument type `T1`, the return type `T2`, and
  `ρ` ― the set of effects that calling the function may yield. Hence, the arrow `->` has the kind
  `Type -> Row Effect -> Type -> Type`.

### 2.1.1 The Kind Syntax

The syntax for kinds is given as the following BNF grammar of three layers with a supplemental element
category:

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

### 2.1.2 Kind Well-formedness

**Kind well-formedness** is a two-way judgement between `Γ` (a local context whose accurate
definition is given in later section of Typing Rules) and a kind `κ` of the form `Γ ⊢ κ kind`.
It means that in local context `Γ`, `κ` is a valid kind.

The kind well-formedness is given by the following rules:

```plain
 -------------- KW-Type               ---------------- KW-Effect
  Γ⊢ Type kind                         Γ⊢ Effect kind

  k ∈ Γ                             Γ ⊢ κ1 kind    Γ ⊢ κ2 kind
 --------- KW-KVar                  ---------------------------- KW-TyCtor
 Γ⊢ k kind                              Γ ⊢ (κ1 -> κ2) kind

   κ element
 ---------------- KW-RowElem
 Γ⊢ (Row κ) kind
```

Here, `k ∈ Γ` means `k` is a bound kind variable in the context `Γ`.
The final rule **KW-RowElem** immediately implies that well-formed row kind is restricted
to the form of either `Row Type` or `Row Effect`, and others are not.

### 2.1.3 The Syntax for Types

Next, we describe the syntax of types in Stella.

Formally, the syntax is given by the following grammar:

```text
τ, σ, ρ ::= a                        type variable
          | T [[κ̄]]                  type constructor; `T` when κ̄ is empty
          | τ1 τ2                    type application
          | forall (a : κ) . τ       universal quantification
          | C => τ                   constraint abstraction, erased
          | ()                       the empty row
          | ( ent | ρ )              row extension
          | ρ1 ⊎ ρ2                  row union

ent ::= k : τ                        a `Row Type` element; the key is written
      | E τ̄                          a `Row Effect` element; the key is derived
      | SymbolKey s : E τ̄            a labelled `Row Effect` element
      | region ℓ                     the region named ℓ is open (D36)

k   ::= a RowKey                     one of the five constructors above
s   ::= a Symbol                     the written name of a labelled element
ℓ   ::= a RegionName                 bound by a `region` of the term

C ::= k ∉ ρ                          Lacks
    | ρ1 # ρ2                        Disjoint```


## 2.2 Row

## 2.3 Effects


## 2.4 Typing Rules

## 2.5 Reduction Rules

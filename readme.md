# MyOwnTT
This implementation was inspired by and expands on Jon Sterling's video lecture:
[How to code your own type theory](https://youtu.be/DEj-_k2Nx6o)

The focus of this program is to elaborate a `surface` language directly emitted by the parser down to a type-correct representation called `syntax`. On the way we also use a `semantic` domain - which is invariantly β-reduced - in the style of normalization-by-evaluation.

### Some major features/aspects of the implementation:
(x) Full spectrum dependent type theory featuring Π and Σ type formers
(x) Normalization by Evaluation w/ DeBruijn levels & indices
(x) Type directed conversion checking
(?) Glued evaluation [2.5hr]
    - test if actually works
        - in conversion
            - conversion of two glues
            - conversion of glued and non-glued
    - lazy environment
        - reform environments in general bc they suck
(x) Bidirectional type checking
(⅘) Parsing and pretty printing
    - change records to `{}`
    - context&precedence-aware pretty printing [2hr]
( ) QoL [3hr]
    - lambda annotations
    - inferring lets
    - function definition sugar
    - error reporting [2hr]
        - catch in `exec`
        - error location
        - parser errors
        - type checking (trace?)
        - conversion ("could not equate A ≡ B when checking X has type Y")
        - internals
    - nested & line comments
(x) Boolean literals
( ) Natural numbers [1hr]
    - parse
    - induction
    - recursion sugar
(⅔) Named tuples [1hr]
    - typed binders?
    - type dependency
    - dictionary annotations
(½) REPL & File input [2hr]
    - #check
    - #conv
    - #unfold
    - elaborate file
    - nested comments
    - indentation aware parsing
    - entire repl [1hr]
        - parse
        - typecheck
        - normalize
        - define vars in environment
        - load defs from file
( ) Refactoring
    - separate module for scenes
    - safe closures and multiclosures
    - uniform typed binders & closures
    - execution module
    - does LET still need a scope?
    - use scope specifier in enviornment (also turn environment to a normal list)
    - rename Rcd, Dict to Sig, Rcd or Sig, Struct...


## Surface
Surface expressions are the direct output from the parser. These use user-friendly explicit naming and distinguish top-level definitions from local let bindings.

## Syntax
Syntactic terms use DeBruijn *indices* (counting the environment from the right) for easy α-equivalence checking.

## Semantics
Semantic values use DeBruijn *levels* (counting the environment from the left) which allows us to freely move expressions deeper into a nested context (aka weakening). This is essential for efficiently β-reducing lambda abstractions, substituting let bindings, etc during evaluation.

### Neutral Values
Values have a distinct subdomain for *neutrals*, which are those values that can't be β-reduced further due to being "stuck" on a variable. These neutrals are represented in spine form for easy access to the head - the variable it's stuck on.
### Glued Eval
During conversion checking we don't necessarily want to unfold all definitions, because that might lead to a significant blow-up in value size. Likewise, when printing values to the user we want them to be as small as possible, for better readability. On the other hand, we still want to be able to unfold all definitions on demand when the need arises. For this we keep a "glued" lazily-evaluated version of the value in which certain definitions can be unfolded.

## Normalization by Evaluation
During type checking we often want to check whether two terms are αβη-convertible to each other. α equivalence is already covered by indices. To handle β reductions we choose a representative for each equivalence class, which is fully β-reduced. This representative is a semantic value, and the process of finding the representative of a term is called *evaluation*.
We also have a reverse operation called *quoting* to go back from the semantic domain to terms.

## Conversion Checking
The last missing piece is η-equivalence. Values are already in η-short form, meaning all the possible η-reductions were applied, but two values might be convertible by applying an η-*expansion* on a neutral value. Conversion checking takes care of this.
Performing η-expansion relies on the type of the values being compared, thus we require *type-directed* conversion checking. This also means we need to carry around some type info within neutrals.

## Bidirectional Elaboration
A typical bidirectional type checker will revolve around the two functions
```
infer : ctx → expr       → Maybe typ
check : ctx → expr → typ → Maybe ()
```
`infer` tries to deduce the type of an expression under a given context, while `check` just attempts to confirm the expression has a given type.

The checker here is actually an *elaborator*, so it spits out a new "type-checked" version of the input expression:
```
infer : ctx → expr       → Maybe (term, typ)
check : ctx → expr → typ → Maybe term
```
In our specific case the elaborated output won't be significantly different from the input, but in more advanced implemetation it is essential to allow modifying the input terms for subsequent parts of the compiler.
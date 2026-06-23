# sml-modal

[![CI](https://github.com/sjqtentacles/sml-modal/actions/workflows/ci.yml/badge.svg)](https://github.com/sjqtentacles/sml-modal/actions/workflows/ci.yml)

**Propositional modal logic** in pure Standard ML over the four classical
frame classes **K, T, S4, S5**: a parser, pretty-printer, Kripke semantics, and
two independent validity engines that must agree on every input —

- a **prefixed analytic tableau** (Fitting-style), and
- **bounded finite Kripke model enumeration**, which exploits the finite-model
  property (a counter-model, if one exists, is found within a small world
  bound).

The two engines are cross-checked by `isValid`, which runs both and raises
`Disagree` if they ever differ. They never do on the test corpus.

The modal operators carry the standard philosophical readings exposed through
`Reading`: `Box` as epistemic *knows* or deontic *ought*, `Dia` as *possible*
or *permitted*.

No FFI, no threads, no clock, no randomness: deterministic and byte-identical
under **MLton** and **Poly/ML**.

## Frame classes

| Class | Accessibility relation                    | Characteristic axiom        |
|-------|-------------------------------------------|-----------------------------|
| `K`   | no constraints                            | `[](p -> q) -> ([]p -> []q)`|
| `T`   | reflexive                                 | `[]p -> p`                  |
| `S4`  | reflexive + transitive                    | `[]p -> [][]p`              |
| `S5`  | reflexive + transitive + symmetric        | `<>p -> []<>p`              |

Each class extends the one above, so every `K`-theorem is a `T`-theorem, every
`T`-theorem an `S4`-theorem, and so on.

## Types

```sml
datatype form =
    Var of string
  | Not of form
  | And of form * form
  | Or  of form * form
  | Imp of form * form           (* -> *)
  | Iff of form * form           (* <-> *)
  | Box of form                  (* [] *)
  | Dia of form                  (* <> *)
  | Top                          (* true  *)
  | Bot                          (* false *)

datatype frame = K | T | S4 | S5

type model = { worlds : int, access : (int * int) list,
               val_ : int * string -> bool }
```

## Concrete syntax

Loosest to tightest binding:

| Syntax        | Meaning              | Associativity |
|---------------|----------------------|---------------|
| `<->`         | biconditional        | right         |
| `->`          | implication          | right         |
| `\|`          | disjunction          | left          |
| `&`           | conjunction          | left          |
| `~`           | negation (prefix)    | —             |
| `[]` / `box`  | Box / necessity      | prefix        |
| `<>` / `dia`  | Dia / possibility    | prefix        |
| `true`/`false`| top / bottom         | —             |
| `( ... )`     | grouping             | —             |

Variables are identifiers (letter or underscore, then alphanumerics or
underscores). `pretty` round-trips: `parse (pretty f)` equals `f` up to
redundant parentheses, rendering `Box` as `[]` and `Dia` as `<>`.

## API

```sml
structure Modal : sig
  datatype form = Var of string | Not of form | And of form * form
    | Or of form * form | Imp of form * form | Iff of form * form
    | Box of form | Dia of form | Top | Bot
  datatype frame = K | T | S4 | S5
  exception Parse of string

  val parse  : string -> form
  val pretty : form -> string
  val vars   : form -> string list   (* sorted, de-duplicated *)
  val size   : form -> int           (* number of distinct subformulas *)

  (* validity engines *)
  val validTableau : frame -> form -> bool   (* Engine A: prefixed tableau *)
  val validModels  : frame -> form -> bool   (* Engine B: model enumeration *)

  (* runs both engines; raises Disagree if they differ *)
  exception Disagree of string
  val isValid       : frame -> form -> bool
  val isSatisfiable : frame -> form -> bool

  (* Kripke semantics *)
  type model = { worlds : int, access : (int * int) list,
                 val_ : int * string -> bool }
  val force          : model -> int -> form -> bool
  val frameSatisfies : frame -> model -> bool

  (* epistemic / deontic readings (identical operators) *)
  structure Reading : sig
    val knows    : form -> form   (* = Box *)
    val possible : form -> form   (* = Dia *)
    val ought    : form -> form   (* = Box *)
    val permitted: form -> form   (* = Dia *)
  end
end
```

## Example

```sml
val k = Modal.parse "[](p -> q) -> ([]p -> []q)"
val true  = Modal.isValid Modal.K  k    (* K axiom holds everywhere *)

val t = Modal.parse "[]p -> p"
val false = Modal.isValid Modal.K  t    (* T axiom fails in K *)
val true  = Modal.isValid Modal.T  t    (* but holds in T and up *)

(* Kripke model: worlds {0,1}, access {0->1}, p true only at world 1 *)
val M = { worlds = 2, access = [(0,1)],
          val_ = fn (w,x) => w = 1 andalso x = "p" }
val true  = Modal.force M 0 (Modal.parse "[]p")   (* all successors have p *)
val false = Modal.force M 1 (Modal.parse "<>p")   (* world 1 has no successor *)
```

Running [`examples/demo.sml`](examples/demo.sml) with `make example` prints:

```
------------------------------------------------------------
1. Parsing and pretty-printing
------------------------------------------------------------
  parse/pretty: []p -> p
    -> []p -> p
  parse/pretty: [](p -> q) -> ([]p -> []q)
    -> [](p -> q) -> []p -> []q
  parse/pretty: <>p <-> ~[]~p
    -> <>p <-> ~[]~p
  parse/pretty: box (p & q) -> dia r
    -> [](p & q) -> <>r
------------------------------------------------------------
2. Variables and size
------------------------------------------------------------
  vars([[]p -> p]) = [p]  size=3
  vars([[](p -> q) -> ([]p -> []q)]) = [p,q]  size=8
  vars([<>(p | q | r)]) = [p,q,r]  size=6
------------------------------------------------------------
3. Kripke semantics: force on a hand-built model
------------------------------------------------------------
  model: worlds {0,1}, access {0->1}, p true only at world 1
  force M 0 (p) = false
  force M 0 ([]p) = true
  force M 0 (<>p) = true
  force M 1 ([]p) = true
  force M 1 (<>p) = false
------------------------------------------------------------
4. The K axiom is valid in every frame class
------------------------------------------------------------
  K: [](p -> q) -> ([]p -> []q)  is valid
  T: [](p -> q) -> ([]p -> []q)  is valid
  S4: [](p -> q) -> ([]p -> []q)  is valid
  S5: [](p -> q) -> ([]p -> []q)  is valid
------------------------------------------------------------
5. []p -> p is valid in T but not in K
------------------------------------------------------------
  K : []p -> p  is not valid
  T : []p -> p  is valid
  S4: []p -> p  is valid
  S5: []p -> p  is valid
------------------------------------------------------------
6. Characteristic axioms across the hierarchy
------------------------------------------------------------
  T  axiom  []p -> p
      K=not valid  T=valid  S4=valid  S5=valid
  4  axiom  []p -> [][]p
      K=not valid  T=not valid  S4=valid  S5=valid
  B  axiom  p -> []<>p
      K=not valid  T=not valid  S4=not valid  S5=valid
  5  axiom  <>p -> []<>p
      K=not valid  T=not valid  S4=not valid  S5=valid
------------------------------------------------------------
7. An S5 theorem, checked by both engines
------------------------------------------------------------
  Formula : <>p -> []<>p
  Tableau : valid
  Models  : valid
  isValid : valid (engines agree)
------------------------------------------------------------
8. Epistemic / deontic readings (Reading)
------------------------------------------------------------
  knows p     = []p
  possible p  = <>p
  ought p     = []p
  permitted p = <>p
------------------------------------------------------------
Done.
------------------------------------------------------------
```

## Build & test

Requires [MLton](http://mlton.org/) and/or [Poly/ML](https://polyml.org/).

```sh
make test        # build + run the suite under MLton
make test-poly   # run the suite under Poly/ML
make all-tests   # both
make example     # build + run the demo
make clean
```

## Installing with smlpkg

```sh
smlpkg add github.com/sjqtentacles/sml-modal
smlpkg sync
```

`sml-modal` vendors [`sml-logic`](https://github.com/sjqtentacles/sml-logic)
under `lib/github.com/sjqtentacles/sml-logic/`. Reference
`lib/github.com/sjqtentacles/sml-modal/sources.mlb` from your own `.mlb`
(MLton / MLKit), or feed `test/sources.mlb` to `tools/polybuild` (Poly/ML).

## Layout

```
sml.pkg                                      smlpkg manifest (requires sml-logic)
Makefile                                     MLton + Poly/ML targets
.github/workflows/ci.yml                     CI: MLton + Poly/ML
lib/github.com/sjqtentacles/
  sml-modal/  modal.sig modal.sml sources.mlb
  sml-logic/  vendored propositional-logic library
examples/
  demo.sml      parser, force, K/T/S4/S5 validity, S5 theorem, readings
test/
  harness.sml / test.sml                     175 reference checks
  entry.sml / main.sml
tools/polybuild                              Poly/ML build wrapper
```

## Tests

175 deterministic checks across 10 sections:

- **Parser / pretty round-trip** (21): every connective and modal operator;
  `pretty . parse` stable under re-parsing; associativity and parenthesization.
- **vars / size** (5): sorted, de-duplicated variable names; subformula count.
- **force** (12): `Box` / `Dia` semantics on hand-built Kripke models, including
  vacuous truth at dead-end worlds.
- **frameSatisfies** (9): reflexive, transitive and symmetric relation checks
  for each class.
- **Per-frame theorems** (13): the K, T, S4 and S5 characteristic axioms, valid
  in their stated class (verified by *both* engines).
- **Per-frame non-theorems** (7): axioms that fail below their class — `[]p -> p`
  not in K, `[]p -> [][]p` not in T, `<>p -> []<>p` not in S4, `p -> []p`
  nowhere.
- **Engine agreement** (48): a 12-formula corpus across all four frames, asserting
  `validTableau frame f = validModels frame f` — the flagship cross-check.
- **isValid** (51): runs both engines without raising `Disagree` on the corpus,
  plus the K/T discrimination.
- **isSatisfiable** (5): `p` satisfiable, `p & ~p` not, etc.
- **Reading** (4): epistemic / deontic aliases.

Run `make all-tests` to verify identical output under both compilers.

## License

MIT. See [LICENSE](LICENSE).

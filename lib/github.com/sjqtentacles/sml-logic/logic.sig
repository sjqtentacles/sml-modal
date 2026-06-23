(* logic.sig

   A propositional-logic toolkit in pure Standard ML: a concrete-syntax parser
   and pretty-printer, truth tables, the tautology / satisfiability /
   equivalence decision procedures, and normal-form transforms (NNF, CNF, DNF).

   Dependency-free: the parser is a small hand-rolled recursive-descent parser
   living inside this library (no external parser-combinator dependency is
   vendored).  No FFI, threads, clock or randomness: the same inputs always
   produce the same outputs under MLton and Poly/ML.

   Concrete syntax accepted by `parse`, from loosest to tightest binding:

       <->, <=>      biconditional (IFF)     right-associative
       ->,  =>       implication   (IMP)     right-associative
       |,   ||       disjunction   (OR)      left-associative
       &,   &&       conjunction   (AND)     left-associative
       !,   ~        negation      (NOT)     prefix, tightest
       ( ... )       grouping
       1 / true      the constant TrueP
       0 / false     the constant FalseP
       identifiers   variables (letter/underscore then alnum/underscore)

   `pretty` round-trips: `parse (pretty p)` is logically equivalent to `p`
   (constants render as `1`/`0`). *)

signature LOGIC =
sig
  datatype prop =
      Var of string
    | Not of prop
    | And of prop * prop
    | Or  of prop * prop
    | Imp of prop * prop
    | Iff of prop * prop
    | TrueP
    | FalseP

  exception Parse of string

  val parse  : string -> prop
  val pretty : prop -> string

  (* sorted, de-duplicated variable names *)
  val vars   : prop -> string list

  (* evaluate under an environment mapping variable names to booleans *)
  val eval   : (string -> bool) -> prop -> bool

  (* every assignment over `vars p` (in sorted order), paired with the value;
     rows run from all-false to all-true. *)
  val truthTable : prop -> (((string * bool) list) * bool) list

  val isTautology    : prop -> bool
  val isContradiction : prop -> bool
  val isSatisfiable  : prop -> bool

  (* logically equivalent over the union of their variables *)
  val equiv  : prop -> prop -> bool

  (* normal forms (all truth-table-preserving) *)
  val toNNF  : prop -> prop   (* negations only on variables *)
  val toCNF  : prop -> prop   (* conjunction of disjunctions *)
  val toDNF  : prop -> prop   (* disjunction of conjunctions *)
end

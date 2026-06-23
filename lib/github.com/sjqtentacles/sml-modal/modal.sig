(* modal.sig

   Propositional modal logic in pure Standard ML, over the four classical
   frame classes K, T, S4 and S5, with two independent validity engines that
   must agree:

     - a prefixed analytic tableau (Fitting-style), and
     - bounded finite Kripke model enumeration (the engine exploits the
       finite-model property: each class has a small-model bound as a function
       of the number of subformulas).

   FORMULAS
   --------
   Propositional variables, the usual connectives, plus the unary modal
   operators Box (necessity) and Dia (possibility).  Dia phi is *not* taken as
   primitive notation for ~Box~phi by the parser, but the two are provably
   equivalent in every class here.

   FRAME CLASSES
   -------------
       K   no constraints on the accessibility relation
       T   reflexive                         (Box p -> p)
       S4  reflexive + transitive            (Box p -> Box Box p)
       S5  reflexive + transitive + symmetric / equivalence
                                             (Dia p -> Box Dia p)

   These also carry the standard philosophical readings: Box as epistemic
   "knows" (S4/S5), as deontic "ought" (KD/K + seriality — see `Deontic`
   aliases), or alethic "necessarily".

   CONCRETE SYNTAX (loosest to tightest)
   -------------------------------------
       <->   biconditional   right-assoc
       ->    implication     right-assoc
       |     disjunction     left-assoc
       &     conjunction     left-assoc
       ~     negation        prefix
       []    Box             prefix (also `box`)
       <>    Dia             prefix (also `dia`)
       true / false
       ( ... )

   DETERMINISM
   -----------
   No FFI, threads, clock or randomness.  Tableau rule selection and model
   enumeration are both in a fixed deterministic order, so the same inputs
   always produce the same outputs under MLton and Poly/ML.
*)

signature MODAL =
sig
  datatype form =
      Var of string
    | Not of form
    | And of form * form
    | Or  of form * form
    | Imp of form * form
    | Iff of form * form
    | Box of form
    | Dia of form
    | Top
    | Bot

  datatype frame = K | T | S4 | S5

  exception Parse of string

  val parse  : string -> form
  val pretty : form -> string

  (* sorted, de-duplicated propositional variable names *)
  val vars   : form -> string list

  (* number of distinct subformulas (drives the model bound) *)
  val size   : form -> int

  (* ------------------------------------------------------------------ engines *)

  (* Engine A: prefixed analytic tableau. true iff `f` is valid in `frame`. *)
  val validTableau : frame -> form -> bool

  (* Engine B: bounded finite Kripke model enumeration. true iff no
     counter-model with up to the class small-model bound falsifies `f`. *)
  val validModels  : frame -> form -> bool

  (* ------------------------------------------------------------------ combined *)

  (* Runs both engines; raises Fail if they disagree (the flagship invariant).
     Otherwise returns their common answer. *)
  exception Disagree of string
  val isValid : frame -> form -> bool

  (* dual: satisfiable in the class iff not valid of the negation *)
  val isSatisfiable : frame -> form -> bool

  (* ------------------------------------------------------------------ semantics *)
  (* A finite Kripke model: worlds 0..n-1, an accessibility relation as a list
     of (from,to) pairs, and a valuation (world * varname -> bool). *)
  type model = { worlds : int, access : (int * int) list,
                 val_ : int * string -> bool }

  (* force M w phi : does world w of model M satisfy phi? *)
  val force : model -> int -> form -> bool

  (* does `frame` allow `model` (its accessibility relation meets the class
     conditions, restricted to its worlds)? *)
  val frameSatisfies : frame -> model -> bool

  (* ------------------------------------------------------------------ deontic/epistemic aliases *)
  (* documented readings; identical operators, exposed for clarity *)
  structure Reading :
  sig
    val knows    : form -> form   (* = Box, epistemic *)
    val possible : form -> form   (* = Dia *)
    val ought    : form -> form   (* = Box, deontic *)
    val permitted: form -> form   (* = Dia, deontic *)
  end
end

(* examples/demo.sml — sml-modal demonstration *)

val () =
let
  val line = String.implode (List.tabulate (60, fn _ => #"-"))
  fun section s = print (line ^ "\n" ^ s ^ "\n" ^ line ^ "\n")
  fun pr s = print (s ^ "\n")

  fun frameName Modal.K  = "K"
    | frameName Modal.T  = "T"
    | frameName Modal.S4 = "S4"
    | frameName Modal.S5 = "S5"

  fun yn true  = "valid"
    | yn false = "not valid"
in

  (* ------------------------------------------------------------------ *)
  section "1. Parsing and pretty-printing"
  ; let val formulas =
          [ "[]p -> p"
          , "[](p -> q) -> ([]p -> []q)"
          , "<>p <-> ~[]~p"
          , "box (p & q) -> dia r"
          ]
    in  List.app (fn s =>
          let val f = Modal.parse s
              val pp = Modal.pretty f
          in  pr ("  parse/pretty: " ^ s); pr ("    -> " ^ pp) end)
          formulas
    end

  (* ------------------------------------------------------------------ *)
  ; section "2. Variables and size"
  ; let val examples =
          [ "[]p -> p"
          , "[](p -> q) -> ([]p -> []q)"
          , "<>(p | q | r)"
          ]
    in  List.app (fn s =>
          let val f = Modal.parse s
          in  pr ("  vars([" ^ s ^ "]) = [" ^
                  String.concatWith "," (Modal.vars f) ^ "]  size=" ^
                  Int.toString (Modal.size f))
          end)
          examples
    end

  (* ------------------------------------------------------------------ *)
  ; section "3. Kripke semantics: force on a hand-built model"
  ; let
      (* worlds {0,1}, accessibility {0->1}; p holds only at world 1 *)
      val M = { worlds = 2, access = [(0,1)],
                val_ = fn (w,x) => w = 1 andalso x = "p" }
      fun show w s =
        pr ("  force M " ^ Int.toString w ^ " (" ^ s ^ ") = " ^
            Bool.toString (Modal.force M w (Modal.parse s)))
    in
      pr "  model: worlds {0,1}, access {0->1}, p true only at world 1"
    ; show 0 "p"
    ; show 0 "[]p"
    ; show 0 "<>p"
    ; show 1 "[]p"
    ; show 1 "<>p"
    end

  (* ------------------------------------------------------------------ *)
  ; section "4. The K axiom is valid in every frame class"
  ; let val k = Modal.parse "[](p -> q) -> ([]p -> []q)"
    in  List.app (fn fr =>
          pr ("  " ^ frameName fr ^ ": [](p -> q) -> ([]p -> []q)  is "
              ^ yn (Modal.isValid fr k)))
          [Modal.K, Modal.T, Modal.S4, Modal.S5]
    end

  (* ------------------------------------------------------------------ *)
  ; section "5. []p -> p is valid in T but not in K"
  ; let val t = Modal.parse "[]p -> p"
    in  pr ("  K : []p -> p  is " ^ yn (Modal.isValid Modal.K  t))
      ; pr ("  T : []p -> p  is " ^ yn (Modal.isValid Modal.T  t))
      ; pr ("  S4: []p -> p  is " ^ yn (Modal.isValid Modal.S4 t))
      ; pr ("  S5: []p -> p  is " ^ yn (Modal.isValid Modal.S5 t))
    end

  (* ------------------------------------------------------------------ *)
  ; section "6. Characteristic axioms across the hierarchy"
  ; let val rows =
          [ ("T  axiom", "[]p -> p")
          , ("4  axiom", "[]p -> [][]p")
          , ("B  axiom", "p -> []<>p")
          , ("5  axiom", "<>p -> []<>p")
          ]
    in  List.app (fn (name, s) =>
          let val f = Modal.parse s
          in pr ("  " ^ name ^ "  " ^ s)
           ; pr ("      K=" ^ yn (Modal.isValid Modal.K f)
                 ^ "  T=" ^ yn (Modal.isValid Modal.T f)
                 ^ "  S4=" ^ yn (Modal.isValid Modal.S4 f)
                 ^ "  S5=" ^ yn (Modal.isValid Modal.S5 f))
          end)
          rows
    end

  (* ------------------------------------------------------------------ *)
  ; section "7. An S5 theorem, checked by both engines"
  ; let val f = Modal.parse "<>p -> []<>p"
    in  pr ("  Formula : " ^ Modal.pretty f)
      ; pr ("  Tableau : " ^ yn (Modal.validTableau Modal.S5 f))
      ; pr ("  Models  : " ^ yn (Modal.validModels  Modal.S5 f))
      ; pr ("  isValid : " ^ yn (Modal.isValid Modal.S5 f) ^ " (engines agree)")
    end

  (* ------------------------------------------------------------------ *)
  ; section "8. Epistemic / deontic readings (Reading)"
  ; let val p = Modal.parse "p"
    in  pr ("  knows p     = " ^ Modal.pretty (Modal.Reading.knows p))
      ; pr ("  possible p  = " ^ Modal.pretty (Modal.Reading.possible p))
      ; pr ("  ought p     = " ^ Modal.pretty (Modal.Reading.ought p))
      ; pr ("  permitted p = " ^ Modal.pretty (Modal.Reading.permitted p))
    end

  (* ------------------------------------------------------------------ *)
  ; section "Done."

end

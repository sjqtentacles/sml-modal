(*  test.sml — comprehensive test suite for sml-modal
    Written BEFORE the implementation (TDD).

    Covers:
      1. Parser / pretty-printer round-trip (connectives + modal operators)
      2. vars (sorted, de-duplicated) and size
      3. force on hand-built Kripke models (Box / Dia semantics)
      4. frameSatisfies on reflexive / transitive / symmetric examples
      5. Per-frame theorem tables (must be valid in the stated class)
      6. Per-frame NON-theorems (must NOT be valid in the stated class)
      7. AGREEMENT: validTableau == validModels across a corpus (flagship)
      8. isValid returns the agreed value and does not raise on the corpus
      9. isSatisfiable basic checks
     10. Reading aliases
*)

structure Tests =
struct
  open Harness

  (* parse shorthand *)
  val pf = Modal.parse

  fun frameName Modal.K  = "K"
    | frameName Modal.T  = "T"
    | frameName Modal.S4 = "S4"
    | frameName Modal.S5 = "S5"

  (* ------------------------------------------------------------------ 1. round-trip *)
  (* pretty(parse s) should be stable under re-parsing: parse it again and
     pretty again, get the same string. *)
  fun rt s = Modal.pretty (Modal.parse (Modal.pretty (Modal.parse s)))
  fun firstPretty s = Modal.pretty (Modal.parse s)

  fun testRoundTrip () =
  ( section "Parser / pretty round-trip"
  ; checkString "var"        ("p", firstPretty "p")
  ; checkString "top"        ("true", firstPretty "true")
  ; checkString "bot"        ("false", firstPretty "false")
  ; checkString "not"        ("~p", firstPretty "~p")
  ; checkString "and"        ("p & q", firstPretty "p & q")
  ; checkString "or"         ("p | q", firstPretty "p | q")
  ; checkString "imp"        ("p -> q", firstPretty "p -> q")
  ; checkString "iff"        ("p <-> q", firstPretty "p <-> q")
  ; checkString "box"        ("[]p", firstPretty "[]p")
  ; checkString "dia"        ("<>p", firstPretty "<>p")
  ; checkString "box word"   ("[]p", firstPretty "box p")
  ; checkString "dia word"   ("<>p", firstPretty "dia p")
  ; checkString "box of imp" ("[](p -> q)", firstPretty "[](p -> q)")
  ; checkString "K axiom"    ("[](p -> q) -> []p -> []q",
                              firstPretty "[](p -> q) -> ([]p -> []q)")
  ; checkString "nested modal" ("[]<>p", firstPretty "[]<>p")
  ; checkString "deep"       ("<>[]<>p", firstPretty "<>[]<>p")
  (* stability: pretty . parse is idempotent through a second round *)
  ; check "stable iff"  (firstPretty "p <-> q & r" = rt "p <-> q & r")
  ; check "stable imp"  (firstPretty "p -> q -> r" = rt "p -> q -> r")
  ; check "stable mix"  (firstPretty "[](p & q) -> <>r" = rt "[](p & q) -> <>r")
  ; check "stable assoc"(firstPretty "p & q & r" = rt "p & q & r")
  ; check "stable orass"(firstPretty "p | q | r" = rt "p | q | r")
  )

  (* ------------------------------------------------------------------ 2. vars / size *)
  fun testVarsSize () =
  ( section "vars / size"
  ; checkStringList "sorted deduped" (["p","q","r"], Modal.vars (pf "r & p | q & p -> r"))
  ; checkStringList "single"        (["p"], Modal.vars (pf "[]p -> p"))
  ; checkStringList "none"          ([], Modal.vars (pf "true -> false"))
  ; check "size positive" (Modal.size (pf "[]p -> p") > 0)
  ; check "size mono"     (Modal.size (pf "[](p & q)") > Modal.size (pf "p"))
  )

  (* ------------------------------------------------------------------ 3. force *)
  (* Two worlds: 0 -> 1.  p true only at world 1. *)
  fun mkVal pairs (w, x) = List.exists (fn (w',x') => w'=w andalso x'=x) pairs

  fun testForce () =
  ( section "force (Kripke semantics)"
  ; let
      (* worlds {0,1}, access {(0,1)}, p holds only at 1 *)
      val M = { worlds = 2, access = [(0,1)],
                val_ = mkVal [(1,"p")] }
    in
      check "var at 1"        (Modal.force M 1 (pf "p"))
    ; check "not var at 0"    (not (Modal.force M 0 (pf "p")))
    ; check "box p at 0"      (Modal.force M 0 (pf "[]p"))  (* all successors (just 1) have p *)
    ; check "dia p at 0"      (Modal.force M 0 (pf "<>p"))  (* successor 1 has p *)
    ; check "box p at 1"      (Modal.force M 1 (pf "[]p"))  (* no successors -> vacuously true *)
    ; check "not dia p at 1"  (not (Modal.force M 1 (pf "<>p"))) (* no successors *)
    end
  ; let
      (* worlds {0,1}, access {(0,1)}, q holds nowhere *)
      val M = { worlds = 2, access = [(0,1)], val_ = mkVal [] }
    in
      check "box q false at 0" (not (Modal.force M 0 (pf "[]q")))
    ; check "dia q false at 0" (not (Modal.force M 0 (pf "<>q")))
    ; check "top"              (Modal.force M 0 (pf "true"))
    ; check "not bot"          (not (Modal.force M 0 (pf "false")))
    ; check "and"              (Modal.force M 0 (pf "true & true"))
    ; check "imp"              (Modal.force M 0 (pf "false -> q"))
    end
  )

  (* ------------------------------------------------------------------ 4. frameSatisfies *)
  fun testFrameSatisfies () =
  ( section "frameSatisfies"
  ; let val refl = { worlds = 2, access = [(0,0),(1,1),(0,1)], val_ = mkVal [] }
    in
      check "K accepts anything" (Modal.frameSatisfies Modal.K refl)
    ; check "T reflexive ok"     (Modal.frameSatisfies Modal.T refl)
    end
  ; let val notRefl = { worlds = 2, access = [(0,1)], val_ = mkVal [] }
    in
      check "T rejects non-reflexive" (not (Modal.frameSatisfies Modal.T notRefl))
    ; check "K still accepts"         (Modal.frameSatisfies Modal.K notRefl)
    end
  ; let (* reflexive but not transitive: 0->1, 1->2, missing 0->2 *)
        val notTrans = { worlds = 3,
                         access = [(0,0),(1,1),(2,2),(0,1),(1,2)],
                         val_ = mkVal [] }
    in
      check "T accepts (reflexive)"        (Modal.frameSatisfies Modal.T notTrans)
    ; check "S4 rejects non-transitive"   (not (Modal.frameSatisfies Modal.S4 notTrans))
    end
  ; let (* reflexive + transitive but not symmetric *)
        val notSym = { worlds = 2, access = [(0,0),(1,1),(0,1)], val_ = mkVal [] }
    in
      check "S4 accepts trans+refl"     (Modal.frameSatisfies Modal.S4 notSym)
    ; check "S5 rejects non-symmetric"  (not (Modal.frameSatisfies Modal.S5 notSym))
    end
  ; let (* full equivalence relation *)
        val equiv = { worlds = 2, access = [(0,0),(1,1),(0,1),(1,0)], val_ = mkVal [] }
    in
      check "S5 accepts equivalence" (Modal.frameSatisfies Modal.S5 equiv)
    end
  )

  (* ------------------------------------------------------------------ 5. theorems *)
  fun mustValid frame s =
    check (frameName frame ^ " |= " ^ s) (Modal.validTableau frame (pf s)
                                          andalso Modal.validModels frame (pf s))

  fun testTheorems () =
  ( section "Per-frame theorems (valid in stated class)"
  (* K *)
  ; mustValid Modal.K  "[](p -> q) -> ([]p -> []q)"            (* K axiom *)
  ; mustValid Modal.K  "[](p & q) <-> ([]p & []q)"
  ; mustValid Modal.K  "[]p -> []p"
  (* T (and everything valid in K) *)
  ; mustValid Modal.T  "[]p -> p"
  ; mustValid Modal.T  "p -> <>p"
  ; mustValid Modal.T  "[](p -> q) -> ([]p -> []q)"
  (* S4 *)
  ; mustValid Modal.S4 "[]p -> [][]p"
  ; mustValid Modal.S4 "<><>p -> <>p"
  ; mustValid Modal.S4 "[]p -> p"                              (* inherited from T *)
  (* S5 *)
  ; mustValid Modal.S5 "<>p -> []<>p"
  ; mustValid Modal.S5 "p -> []<>p"
  ; mustValid Modal.S5 "<>[]p -> []p"
  ; mustValid Modal.S5 "[]p -> [][]p"                          (* inherited from S4 *)
  )

  (* ------------------------------------------------------------------ 6. non-theorems *)
  fun mustInvalid frame s =
    check (frameName frame ^ " |/= " ^ s) (not (Modal.validTableau frame (pf s))
                                           andalso not (Modal.validModels frame (pf s)))

  fun testNonTheorems () =
  ( section "Per-frame non-theorems (NOT valid in stated class)"
  ; mustInvalid Modal.K  "[]p -> p"            (* T axiom, not valid in K *)
  ; mustInvalid Modal.T  "[]p -> [][]p"        (* S4 axiom, not valid in T *)
  ; mustInvalid Modal.S4 "<>p -> []<>p"        (* S5 axiom, not valid in S4 *)
  ; mustInvalid Modal.K  "p -> []p"
  ; mustInvalid Modal.T  "p -> []p"
  ; mustInvalid Modal.S4 "p -> []p"
  ; mustInvalid Modal.S5 "p -> []p"
  )

  (* ------------------------------------------------------------------ 7. agreement *)
  val corpus =
    [ "[](p -> q) -> ([]p -> []q)"
    , "[](p & q) <-> ([]p & []q)"
    , "[]p -> p"
    , "p -> <>p"
    , "[]p -> [][]p"
    , "<><>p -> <>p"
    , "<>p -> []<>p"
    , "p -> []<>p"
    , "<>[]p -> []p"
    , "p -> []p"
    , "[]p -> <>p"
    , "<>(p | q) -> (<>p | <>q)"
    ]

  val frames = [Modal.K, Modal.T, Modal.S4, Modal.S5]

  fun testAgreement () =
  ( section "Engine agreement (validTableau == validModels)"
  ; List.app (fn fr =>
      List.app (fn s =>
        let val f = pf s
            val a = Modal.validTableau fr f
            val b = Modal.validModels fr f
        in checkBool (frameName fr ^ " " ^ s) (a, b) end)
      corpus)
    frames
  )

  (* ------------------------------------------------------------------ 8. isValid *)
  fun testIsValid () =
  ( section "isValid (runs both, no Disagree on corpus)"
  ; List.app (fn fr =>
      List.app (fn s =>
        check ("isValid ok " ^ frameName fr ^ " " ^ s)
          ((Modal.isValid fr (pf s); true) handle Modal.Disagree _ => false))
      corpus)
    frames
  ; check "isValid K axiom true"  (Modal.isValid Modal.K (pf "[](p -> q) -> ([]p -> []q)"))
  ; check "isValid T axiom in K false" (not (Modal.isValid Modal.K (pf "[]p -> p")))
  ; check "isValid T axiom in T true"  (Modal.isValid Modal.T (pf "[]p -> p"))
  )

  (* ------------------------------------------------------------------ 9. isSatisfiable *)
  fun testSatisfiable () =
  ( section "isSatisfiable"
  ; check "p satisfiable in K"      (Modal.isSatisfiable Modal.K (pf "p"))
  ; check "p&~p unsatisfiable"      (not (Modal.isSatisfiable Modal.K (pf "p & ~p")))
  ; check "[]p & ~[]p unsat"        (not (Modal.isSatisfiable Modal.K (pf "[]p & ~[]p")))
  ; check "<>p satisfiable"         (Modal.isSatisfiable Modal.T (pf "<>p"))
  ; check "[]p -> p sat (valid->sat)" (Modal.isSatisfiable Modal.T (pf "[]p -> p"))
  )

  (* ------------------------------------------------------------------ 10. Reading aliases *)
  fun testReading () =
  ( section "Reading aliases"
  ; check "knows = Box"     (Modal.Reading.knows (pf "p")    = Modal.Box (pf "p"))
  ; check "possible = Dia"  (Modal.Reading.possible (pf "p") = Modal.Dia (pf "p"))
  ; check "ought = Box"     (Modal.Reading.ought (pf "p")    = Modal.Box (pf "p"))
  ; check "permitted = Dia" (Modal.Reading.permitted (pf "p")= Modal.Dia (pf "p"))
  )

  (* ------------------------------------------------------------------ main runner *)
  fun runAll () =
  ( testRoundTrip ()
  ; testVarsSize ()
  ; testForce ()
  ; testFrameSatisfies ()
  ; testTheorems ()
  ; testNonTheorems ()
  ; testAgreement ()
  ; testIsValid ()
  ; testSatisfiable ()
  ; testReading ()
  ; Harness.run ()
  )

  val run = runAll
end

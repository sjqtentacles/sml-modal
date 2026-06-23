(*  modal.sml — propositional modal logic over K / T / S4 / S5.

    Two independent validity engines that must agree:
      - Engine A: prefixed analytic tableau (Fitting-style).
      - Engine B: bounded finite Kripke model enumeration (finite model property).

    Pure and deterministic: no FFI, threads, clock, or randomness.  All exposed
    collections are sorted and de-duplicated for byte-identical output across
    MLton and Poly/ML.
*)

structure Modal :> MODAL =
struct

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
  exception Disagree of string

  (* ================================================================== sorting *)
  fun sortDedupStr xs =
    let
      fun merge ([], ys) = ys
        | merge (xs, []) = xs
        | merge (x :: xs, y :: ys) =
            (case String.compare (x, y) of
               LESS    => x :: merge (xs, y :: ys)
             | GREATER => y :: merge (x :: xs, ys)
             | EQUAL   => x :: merge (xs, ys))   (* drop the duplicate *)
      fun split [] = ([], [])
        | split [x] = ([x], [])
        | split (x :: y :: rest) =
            let val (a, b) = split rest in (x :: a, y :: b) end
      fun msort [] = []
        | msort [x] = [x]
        | msort xs =
            let val (a, b) = split xs
            in merge (msort a, msort b) end
      val sorted = msort xs
      fun dedup [] = []
        | dedup [x] = [x]
        | dedup (x :: y :: rest) =
            if x = y then dedup (y :: rest) else x :: dedup (y :: rest)
    in dedup sorted end

  (* ================================================================== vars / size *)
  fun vars f =
    let
      fun go (Var x)     acc = x :: acc
        | go (Not p)     acc = go p acc
        | go (And (p,q)) acc = go p (go q acc)
        | go (Or  (p,q)) acc = go p (go q acc)
        | go (Imp (p,q)) acc = go p (go q acc)
        | go (Iff (p,q)) acc = go p (go q acc)
        | go (Box p)     acc = go p acc
        | go (Dia p)     acc = go p acc
        | go Top         acc = acc
        | go Bot         acc = acc
    in sortDedupStr (go f []) end

  (* number of distinct subformulas (drives the model bound) *)
  fun size f =
    let
      (* collect subformulas as pretty strings into a sorted-unique count via list *)
      fun subs (Var x)     acc = (Var x) :: acc
        | subs (Not p)     acc = (Not p) :: subs p acc
        | subs (And (p,q)) acc = (And (p,q)) :: subs p (subs q acc)
        | subs (Or  (p,q)) acc = (Or  (p,q)) :: subs p (subs q acc)
        | subs (Imp (p,q)) acc = (Imp (p,q)) :: subs p (subs q acc)
        | subs (Iff (p,q)) acc = (Iff (p,q)) :: subs p (subs q acc)
        | subs (Box p)     acc = (Box p) :: subs p acc
        | subs (Dia p)     acc = (Dia p) :: subs p acc
        | subs Top         acc = Top :: acc
        | subs Bot         acc = Bot :: acc
      val all = subs f []
      (* count distinct by structural equality *)
      fun member x [] = false
        | member x (y :: ys) = (x = y) orelse member x ys
      fun distinct [] seen = seen
        | distinct (x :: xs) seen =
            if member x seen then distinct xs seen else distinct xs (x :: seen)
    in length (distinct all []) end

  (* ================================================================== tokenizer *)
  datatype tok =
      TVar of string
    | TNot | TAnd | TOr | TImp | TIff
    | TBox | TDia | TTop | TBot
    | TLP | TRP

  fun isIdentStart c = Char.isAlpha c orelse c = #"_"
  fun isIdentChar  c = Char.isAlphaNum c orelse c = #"_"

  fun tokenize s =
    let
      val n = String.size s
      fun peek i = if i < n then SOME (String.sub (s, i)) else NONE
      fun lexIdent i j =
        if j < n andalso isIdentChar (String.sub (s, j))
        then lexIdent i (j + 1)
        else (String.substring (s, i, j - i), j)
      fun go i acc =
        if i >= n then List.rev acc
        else
          let val c = String.sub (s, i) in
            if Char.isSpace c then go (i + 1) acc
            else if c = #"(" then go (i + 1) (TLP :: acc)
            else if c = #")" then go (i + 1) (TRP :: acc)
            else if c = #"~" then go (i + 1) (TNot :: acc)
            else if c = #"&" then go (i + 1) (TAnd :: acc)
            else if c = #"|" then go (i + 1) (TOr :: acc)
            else if c = #"[" then
              (case peek (i + 1) of
                 SOME #"]" => go (i + 2) (TBox :: acc)
               | _ => raise Parse "expected ']' after '['")
            else if c = #"<" then
              (case peek (i + 1) of
                 SOME #">" => go (i + 2) (TDia :: acc)
               | SOME #"-" =>
                   (case peek (i + 2) of
                      SOME #">" => go (i + 3) (TIff :: acc)  (* <-> *)
                    | _ => raise Parse "expected '>' in '<->'")
               | _ => raise Parse "unexpected '<'")
            else if c = #"-" then
              (case peek (i + 1) of
                 SOME #">" => go (i + 2) (TImp :: acc)
               | _ => raise Parse "expected '>' after '-'")
            else if isIdentStart c then
              let val (name, j) = lexIdent i i in
                case name of
                  "true"  => go j (TTop :: acc)
                | "false" => go j (TBot :: acc)
                | "box"   => go j (TBox :: acc)
                | "dia"   => go j (TDia :: acc)
                | _       => go j (TVar name :: acc)
              end
            else raise Parse ("unexpected character: " ^ String.str c)
          end
    in go 0 [] end

  (* ================================================================== parser *)
  (* Grammar (loosest to tightest):
       iff   ::= imp ('<->' imp)*           right-assoc
       imp   ::= orE ('->' imp)?            right-assoc
       orE   ::= andE ('|' andE)*           left-assoc
       andE  ::= unary ('&' unary)*         left-assoc
       unary ::= '~' unary | '[]' unary | '<>' unary | atom
       atom  ::= var | true | false | '(' iff ')'                       *)
  fun parse s =
    let
      val toks = tokenize s
      fun expected what = raise Parse ("expected " ^ what)

      fun parseIff ts =
        let val (lhs, ts1) = parseImp ts in
          case ts1 of
            TIff :: rest =>
              let val (rhs, ts2) = parseIff rest in (Iff (lhs, rhs), ts2) end
          | _ => (lhs, ts1)
        end

      and parseImp ts =
        let val (lhs, ts1) = parseOr ts in
          case ts1 of
            TImp :: rest =>
              let val (rhs, ts2) = parseImp rest in (Imp (lhs, rhs), ts2) end
          | _ => (lhs, ts1)
        end

      and parseOr ts =
        let val (lhs, ts1) = parseAnd ts in
          orTail lhs ts1
        end
      and orTail lhs (TOr :: rest) =
            let val (rhs, ts2) = parseAnd rest in orTail (Or (lhs, rhs)) ts2 end
        | orTail lhs ts = (lhs, ts)

      and parseAnd ts =
        let val (lhs, ts1) = parseUnary ts in
          andTail lhs ts1
        end
      and andTail lhs (TAnd :: rest) =
            let val (rhs, ts2) = parseUnary rest in andTail (And (lhs, rhs)) ts2 end
        | andTail lhs ts = (lhs, ts)

      and parseUnary (TNot :: rest) =
            let val (p, ts) = parseUnary rest in (Not p, ts) end
        | parseUnary (TBox :: rest) =
            let val (p, ts) = parseUnary rest in (Box p, ts) end
        | parseUnary (TDia :: rest) =
            let val (p, ts) = parseUnary rest in (Dia p, ts) end
        | parseUnary ts = parseAtom ts

      and parseAtom (TVar x :: rest) = (Var x, rest)
        | parseAtom (TTop :: rest)   = (Top, rest)
        | parseAtom (TBot :: rest)   = (Bot, rest)
        | parseAtom (TLP :: rest) =
            let val (p, ts) = parseIff rest in
              case ts of
                TRP :: rest' => (p, rest')
              | _ => expected "')'"
            end
        | parseAtom _ = expected "an atom"

      val (result, leftover) = parseIff toks
    in
      case leftover of
        [] => result
      | _  => raise Parse "trailing input"
    end

  (* ================================================================== pretty *)
  (* Precedence levels: 0 iff, 1 imp, 2 or, 3 and, 4 unary/atom.
     Parenthesize a child when its precedence is lower than the context, with
     associativity-aware rules so that parse(pretty f) = f modulo redundant parens. *)
  fun pretty f =
    let
      fun prec (Iff _) = 0
        | prec (Imp _) = 1
        | prec (Or  _) = 2
        | prec (And _) = 3
        | prec _       = 4
      (* render f at minimum-precedence `ctx`; paren if prec f < ctx *)
      fun go ctx f =
        let val s = raw f
        in if prec f < ctx then "(" ^ s ^ ")" else s end
      and raw (Var x) = x
        | raw Top = "true"
        | raw Bot = "false"
        | raw (Not p) = "~" ^ go 4 p
        | raw (Box p) = "[]" ^ go 4 p
        | raw (Dia p) = "<>" ^ go 4 p
        | raw (And (a,b)) = go 3 a ^ " & " ^ go 4 b   (* left-assoc: right child tighter *)
        | raw (Or  (a,b)) = go 2 a ^ " | " ^ go 3 b
        | raw (Imp (a,b)) = go 2 a ^ " -> " ^ go 1 b  (* right-assoc: left child tighter *)
        | raw (Iff (a,b)) = go 1 a ^ " <-> " ^ go 0 b
    in go 0 f end

  (* ================================================================== model *)
  type model = { worlds : int, access : (int * int) list,
                 val_ : int * string -> bool }

  fun force (M : model) w f =
    let
      val { worlds = _, access, val_ } = M
      fun succs v = List.foldr (fn ((a,b),acc) => if a = v then b :: acc else acc) [] access
      fun ev w f =
        case f of
          Var x => val_ (w, x)
        | Top => true
        | Bot => false
        | Not p => not (ev w p)
        | And (p,q) => ev w p andalso ev w q
        | Or  (p,q) => ev w p orelse ev w q
        | Imp (p,q) => (not (ev w p)) orelse ev w q
        | Iff (p,q) => ev w p = ev w q
        | Box p => List.all (fn w' => ev w' p) (succs w)
        | Dia p => List.exists (fn w' => ev w' p) (succs w)
    in ev w f end

  (* ================================================================== frameSatisfies *)
  fun frameSatisfies fr (M : model) =
    let
      val { worlds = n, access, ... } = M
      fun rel a b = List.exists (fn (x,y) => x = a andalso y = b) access
      val ws = List.tabulate (n, fn i => i)
      fun reflexive () = List.all (fn w => rel w w) ws
      fun transitive () =
        List.all (fn a => List.all (fn b => List.all (fn c =>
          (not (rel a b andalso rel b c)) orelse rel a c) ws) ws) ws
      fun symmetric () =
        List.all (fn a => List.all (fn b =>
          (not (rel a b)) orelse rel b a) ws) ws
    in
      case fr of
        K  => true
      | T  => reflexive ()
      | S4 => reflexive () andalso transitive ()
      | S5 => reflexive () andalso transitive () andalso symmetric ()
    end

  (* ================================================================== Engine B: validModels *)
  (* Bounded finite-model enumeration.  A formula is valid in a class iff no
     model of that class falsifies it at some world.  By the finite-model
     property each of K/T/S4/S5 has a small-model bound: a counter-model, if
     one exists, can be found with at most (modal-depth + 1) worlds.  We search
     n = 1 .. bound worlds, where bound = min(modalDepth f + 1, maxWorlds),
     enumerating every class-admissible relation and every valuation in a fixed
     deterministic order. *)
  val maxWorlds = 4

  fun modalDepth f =
    case f of
      Var _ => 0
    | Top => 0
    | Bot => 0
    | Not p => modalDepth p
    | And (p,q) => Int.max (modalDepth p, modalDepth q)
    | Or  (p,q) => Int.max (modalDepth p, modalDepth q)
    | Imp (p,q) => Int.max (modalDepth p, modalDepth q)
    | Iff (p,q) => Int.max (modalDepth p, modalDepth q)
    | Box p => 1 + modalDepth p
    | Dia p => 1 + modalDepth p

  fun validModels fr f =
    let
      val ks = vars f
      val k  = length ks
      val bound = Int.min (modalDepth f + 1, maxWorlds)

      (* all pairs on n worlds, in fixed order *)
      fun allPairs n =
        List.concat (List.tabulate (n, fn a =>
          List.tabulate (n, fn b => (a, b))))

      (* enumerate all subsets of a list, fixed order *)
      fun subsets [] = [[]]
        | subsets (x :: xs) =
            let val rest = subsets xs
            in List.concat (List.map (fn s => [s, x :: s]) rest) end

      fun varIndex x =
        let fun find i [] = ~1
              | find i (y :: ys) = if x = y then i else find (i+1) ys
        in find 0 ks end

      (* a valuation is an int bitmask over n*k cells; cell (w,vi) = w*k+vi *)
      fun cellIndex w vi = w * k + vi
      fun bitSet (mask, i) =
        Word.andb (Word.>> (mask, Word.fromInt i), 0w1) = 0w1
      fun mkVal mask (w, x) =
        let val vi = varIndex x
        in if vi < 0 then false else bitSet (mask, cellIndex w vi) end

      fun searchN n =
        if n > bound then false  (* no counter-model found up to bound *)
        else
          let
            val pairs = allPairs n
            val rels = subsets pairs
            (* keep only relations meeting the class condition *)
            fun relOk access =
              frameSatisfies fr { worlds = n, access = access, val_ = fn _ => false }
            val goodRels = List.filter relOk rels
            val cells = n * k
            val nVals = Word.<< (0w1, Word.fromInt cells)   (* 2^cells *)
            val worldsList = List.tabulate (n, fn i => i)
            fun tryRels [] = searchN (n + 1)
              | tryRels (access :: more) =
                  let
                    fun tryVals v =
                      if v >= nVals then tryRels more
                      else
                        let
                          val M = { worlds = n, access = access, val_ = mkVal v }
                          val falsified =
                            List.exists (fn w => not (force M w f)) worldsList
                        in
                          if falsified then true
                          else tryVals (v + 0w1)
                        end
                  in tryVals 0w0 end
          in tryRels goodRels end
    in
      not (searchN 1)
    end

  (* ================================================================== Engine A: validTableau *)
  (* Prefixed analytic tableau (Fitting-style).  To test validity of f, attempt
     to build a closed tableau for ~f; f is valid iff every branch closes.

     Prefixes are int lists; the root is [0]; a child of sigma is (k :: sigma)
     for a fresh k.  Edges record direct parent->child links created by pi
     rules.  The nu (necessity) rule applies a Box body to every prefix
     accessible from sigma under the class closure:
       K  : direct successors
       T  : self + direct successors
       S4 : self + all (transitive) descendants
       S5 : every prefix on the branch (equivalence) *)

  fun validTableau fr f =
    let
      val cap = 200000

      fun prefixEq (a : int list, b : int list) = (a = b)
      fun itemEq ((s1,f1),(s2,f2)) = prefixEq (s1,s2) andalso f1 = f2
      fun hasItem items it = List.exists (fn x => itemEq (x, it)) items

      fun directSucc edges sigma =
        List.foldr (fn ((a,b),acc) => if prefixEq (a, sigma) then b :: acc else acc)
                   [] edges

      fun reachClosure edges sigma =
        let
          fun mem x xs = List.exists (fn y => prefixEq (x,y)) xs
          fun bfs [] seen = seen
            | bfs (x :: xs) seen =
                if mem x seen then bfs xs seen
                else bfs (directSucc edges x @ xs) (x :: seen)
        in bfs (directSucc edges sigma) [] end

      fun accessible prefixes edges sigma =
        case fr of
          K  => directSucc edges sigma
        | T  => sigma :: directSucc edges sigma
        | S4 => sigma :: reachClosure edges sigma
        | S5 => prefixes

      (* a branch closes if it contains (sg,Bot), (sg,~Top), or (sg,A)&(sg,~A) *)
      fun isClosed items =
        List.exists (fn (sg, ff) =>
          case ff of
            Bot => true
          | Not Top => true
          | _ =>
              let val target = (case ff of Not g => g | _ => Not ff)
              in hasItem items (sg, target) end)
          items

      (* alpha: deterministic conjunctive expansion -> list of new items *)
      fun alpha (sg, ff) =
        case ff of
          And (a,b)        => SOME [(sg,a),(sg,b)]
        | Not (Or (a,b))   => SOME [(sg,Not a),(sg,Not b)]
        | Not (Imp (a,b))  => SOME [(sg,a),(sg,Not b)]
        | Not (Not a)      => SOME [(sg,a)]
        | Iff (a,b)        => SOME [(sg, Imp(a,b)),(sg, Imp(b,a))]
        | Not (Iff (a,b))  => SOME [(sg, Not(Imp(a,b))),(sg, Not(Imp(b,a)))]
        | _ => NONE

      (* beta: disjunctive branching -> list of alternative item-lists *)
      fun beta (sg, ff) =
        case ff of
          Or (a,b)        => SOME [[(sg,a)],[(sg,b)]]
        | Imp (a,b)       => SOME [[(sg,Not a)],[(sg,b)]]
        | Not (And (a,b)) => SOME [[(sg,Not a)],[(sg,Not b)]]
        | _ => NONE

      fun piBody ff =
        case ff of Dia a => SOME a | Not (Box a) => SOME (Not a) | _ => NONE
      fun nuBody ff =
        case ff of Box a => SOME a | Not (Dia a) => SOME (Not a) | _ => NONE

      (* Saturate all non-branching rules (alpha, nu) to a fixpoint, returning
         the augmented (items, edges, prefixes, counter).  pi creates a fresh
         world each time it fires (once per distinct pi item, tracked via the
         child it produces). *)
      fun saturate (items, edges, prefixes, counter) =
        let
          (* one alpha step that adds something new *)
          fun alphaStep [] = NONE
            | alphaStep (it :: rest) =
                (case alpha it of
                   SOME news =>
                     let val fresh = List.filter (fn nw => not (hasItem items nw)) news
                     in if null fresh then alphaStep rest else SOME fresh end
                 | NONE => alphaStep rest)
          (* nu: apply every necessity to every accessible prefix *)
          fun nuNew () =
            List.foldr (fn ((sg,ff), acc) =>
              case nuBody ff of
                NONE => acc
              | SOME body =>
                  let val taus = accessible prefixes edges sg
                  in List.foldr (fn (tau, a) =>
                       let val nw = (tau, body)
                       in if hasItem items nw orelse hasItem a nw then a else nw :: a end)
                       acc taus
                  end)
              [] items
        in
          case alphaStep items of
            SOME fresh => saturate (fresh @ items, edges, prefixes, counter)
          | NONE =>
            let val nn = nuNew ()
            in
              if not (null nn)
              then saturate (nn @ items, edges, prefixes, counter)
              else (items, edges, prefixes, counter)
            end
        end

      (* fire all pi items that have not yet produced a successor.  We mark a pi
         item as fired by checking whether some edge from sg leads to a child
         whose item-set already contains the body — simpler: track fired pis in
         a list of (sg, ff). *)
      fun firePis (items, edges, prefixes, counter, fired) =
        let
          fun findPi [] = NONE
            | findPi ((sg,ff) :: rest) =
                (case piBody ff of
                   SOME body =>
                     if List.exists (fn x => itemEq (x,(sg,ff))) fired
                     then findPi rest
                     else SOME (sg, ff, body)
                 | NONE => findPi rest)
        in
          case findPi items of
            NONE => NONE
          | SOME (sg, ff, body) =>
              let
                val child = counter :: sg
                val edges' = (sg, child) :: edges
                val prefixes' = child :: prefixes
                val items' = (child, body) :: items
              in SOME (items', edges', prefixes', counter + 1, (sg,ff) :: fired) end
        end

      (* main loop on a single branch.  steps guards termination. *)
      fun loop steps (items, edges, prefixes, counter, fired) =
        if steps <= 0 then false
        else if isClosed items then true
        else
          let
            val (items, edges, prefixes, counter) =
              saturate (items, edges, prefixes, counter)
          in
            if isClosed items then true
            else
              (* branch on the first beta whose alternatives are not yet present *)
              let
                fun findBeta [] = NONE
                  | findBeta (it :: rest) =
                      (case beta it of
                         SOME branches =>
                           let val satisfied =
                                 List.exists (fn br =>
                                   List.all (fn nw => hasItem items nw) br) branches
                           in if satisfied then findBeta rest else SOME branches end
                       | NONE => findBeta rest)
              in
                case findBeta items of
                  SOME branches =>
                    List.all (fn br =>
                      loop (steps-1) (br @ items, edges, prefixes, counter, fired))
                      branches
                | NONE =>
                  (* no alpha/nu/beta progress: try a pi (creates a world) *)
                  case firePis (items, edges, prefixes, counter, fired) of
                    SOME st => loop (steps-1) st
                  | NONE => false   (* saturated open branch: f is not valid *)
              end
          end

      val root : int list = [0]
    in
      loop cap ([(root, Not f)], [], [root], 1, [])
    end

  (* ================================================================== combined *)
  fun isValid fr f =
    let
      val a = validTableau fr f
      val b = validModels fr f
    in
      if a = b then a
      else raise Disagree ("tableau=" ^ Bool.toString a ^ " models=" ^ Bool.toString b
                           ^ " on " ^ pretty f)
    end

  fun isSatisfiable fr f = not (isValid fr (Not f))

  (* ================================================================== Reading *)
  structure Reading =
  struct
    fun knows p     = Box p
    fun possible p  = Dia p
    fun ought p     = Box p
    fun permitted p = Dia p
  end

end

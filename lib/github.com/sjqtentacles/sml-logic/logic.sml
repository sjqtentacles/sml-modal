(* logic.sml - propositional logic toolkit.

   The parser is a hand-rolled recursive-descent parser over a small token
   stream (no external dependency).  Grammar, loosest to tightest:

       iff  ::= imp ( ('<->'|'<=>') iff )?            right assoc
       imp  ::= orE ( ('->'|'=>')   imp )?            right assoc
       orE  ::= andE ( ('|'|'||')  andE )*            left assoc
       andE ::= notE ( ('&'|'&&')  notE )*            left assoc
       notE ::= ('!'|'~') notE | atom
       atom ::= var | '1'|'true' | '0'|'false' | '(' iff ')'

   Normal forms go through NNF (eliminate ->, <->, push ! to variables), then
   distribute for CNF / DNF. *)

structure Logic :> LOGIC =
struct
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

  (* ---------------------------------------------------------------- *)
  (* tokenizer                                                         *)

  datatype tok =
      TVar of string | TNot | TAnd | TOr | TImp | TIff
    | TLP | TRP | TTrue | TFalse

  fun tokenize s =
    let
      fun isIdStart c = Char.isAlpha c orelse c = #"_"
      fun isIdChar  c = Char.isAlphaNum c orelse c = #"_"
      fun takeId chars =
        let
          fun go (acc, c :: cs) =
                if isIdChar c then go (c :: acc, cs)
                else (String.implode (List.rev acc), c :: cs)
            | go (acc, []) = (String.implode (List.rev acc), [])
        in go ([], chars) end
      fun lex [] = []
        | lex (c :: rest) =
            if Char.isSpace c then lex rest
            else
              case c of
                #"(" => TLP :: lex rest
              | #")" => TRP :: lex rest
              | #"&" => (case rest of #"&" :: r => TAnd :: lex r | _ => TAnd :: lex rest)
              | #"|" => (case rest of #"|" :: r => TOr  :: lex r | _ => TOr  :: lex rest)
              | #"!" => TNot :: lex rest
              | #"~" => TNot :: lex rest
              | #"-" => (case rest of #">" :: r => TImp :: lex r
                                    | _ => raise Parse "expected '>' after '-'")
              | #"=" => (case rest of #">" :: r => TImp :: lex r
                                    | _ => raise Parse "expected '>' after '='")
              | #"<" => (case rest of
                           #"-" :: #">" :: r => TIff :: lex r
                         | #"=" :: #">" :: r => TIff :: lex r
                         | _ => raise Parse "expected '<->' or '<=>'")
              | #"1" => TTrue :: lex rest
              | #"0" => TFalse :: lex rest
              | _ =>
                  if isIdStart c then
                    let val (name, r) = takeId (c :: rest)
                    in (case name of
                          "true"  => TTrue
                        | "false" => TFalse
                        | _ => TVar name) :: lex r
                    end
                  else raise Parse ("unexpected character: " ^ String.str c)
    in lex (String.explode s) end

  (* ---------------------------------------------------------------- *)
  (* recursive descent                                                 *)

  fun parse s =
    let
      val toks = tokenize s

      fun pIff ts =
        let val (a, ts) = pImp ts
        in case ts of
             TIff :: ts' => let val (b, ts2) = pIff ts' in (Iff (a, b), ts2) end
           | _ => (a, ts)
        end
      and pImp ts =
        let val (a, ts) = pOr ts
        in case ts of
             TImp :: ts' => let val (b, ts2) = pImp ts' in (Imp (a, b), ts2) end
           | _ => (a, ts)
        end
      and pOr ts =
        let
          val (a, ts) = pAnd ts
          fun loop (acc, TOr :: ts') =
                let val (b, ts2) = pAnd ts' in loop (Or (acc, b), ts2) end
            | loop (acc, ts') = (acc, ts')
        in loop (a, ts) end
      and pAnd ts =
        let
          val (a, ts) = pNot ts
          fun loop (acc, TAnd :: ts') =
                let val (b, ts2) = pNot ts' in loop (And (acc, b), ts2) end
            | loop (acc, ts') = (acc, ts')
        in loop (a, ts) end
      and pNot (TNot :: ts) = let val (a, ts') = pNot ts in (Not a, ts') end
        | pNot ts = pAtom ts
      and pAtom (TVar v :: ts) = (Var v, ts)
        | pAtom (TTrue :: ts)  = (TrueP, ts)
        | pAtom (TFalse :: ts) = (FalseP, ts)
        | pAtom (TLP :: ts) =
            let val (a, ts') = pIff ts
            in case ts' of
                 TRP :: ts2 => (a, ts2)
               | _ => raise Parse "expected ')'"
            end
        | pAtom [] = raise Parse "unexpected end of input"
        | pAtom _ = raise Parse "expected an atom"

      val (p, rest) = pIff toks
    in
      case rest of [] => p | _ => raise Parse "trailing tokens"
    end

  (* ---------------------------------------------------------------- *)
  (* pretty-printer (minimal parentheses)                              *)

  fun pretty p =
    let
      (* returns (text, precedence): 1 Iff, 2 Imp, 3 Or, 4 And, 5 Not, 6 atom *)
      fun bin (a, b, opS, lvl, rightAssoc) =
        let
          val (sa, pa) = go a
          val (sb, pb) = go b
          val la = if pa < lvl orelse (pa = lvl andalso rightAssoc)
                   then "(" ^ sa ^ ")" else sa
          val rb = if pb < lvl orelse (pb = lvl andalso not rightAssoc)
                   then "(" ^ sb ^ ")" else sb
        in (la ^ " " ^ opS ^ " " ^ rb, lvl) end
      and go TrueP = ("1", 6)
        | go FalseP = ("0", 6)
        | go (Var s) = (s, 6)
        | go (Not q) =
            let val (s, pc) = go q
            in (if pc < 5 then "!(" ^ s ^ ")" else "!" ^ s, 5) end
        | go (And (a, b)) = bin (a, b, "&", 4, false)
        | go (Or (a, b))  = bin (a, b, "|", 3, false)
        | go (Imp (a, b)) = bin (a, b, "->", 2, true)
        | go (Iff (a, b)) = bin (a, b, "<->", 1, true)
    in #1 (go p) end

  (* ---------------------------------------------------------------- *)
  (* variables (sorted, unique)                                        *)

  fun vars p =
    let
      fun ins (x, []) = [x]
        | ins (x, y :: ys) =
            (case String.compare (x, y) of
               LESS => x :: y :: ys
             | EQUAL => y :: ys
             | GREATER => y :: ins (x, ys))
      fun go (TrueP, acc) = acc
        | go (FalseP, acc) = acc
        | go (Var s, acc) = ins (s, acc)
        | go (Not a, acc) = go (a, acc)
        | go (And (a, b), acc) = go (b, go (a, acc))
        | go (Or (a, b), acc)  = go (b, go (a, acc))
        | go (Imp (a, b), acc) = go (b, go (a, acc))
        | go (Iff (a, b), acc) = go (b, go (a, acc))
    in go (p, []) end

  (* ---------------------------------------------------------------- *)
  (* evaluation                                                        *)

  fun eval env =
    let
      fun go TrueP = true
        | go FalseP = false
        | go (Var s) = env s
        | go (Not a) = not (go a)
        | go (And (a, b)) = go a andalso go b
        | go (Or (a, b)) = go a orelse go b
        | go (Imp (a, b)) = (not (go a)) orelse go b
        | go (Iff (a, b)) = (go a = go b)
    in go end

  (* environment from an assignment list, default false for unlisted vars *)
  fun envOf assign s =
    case List.find (fn (k, _) => k = s) assign of
      SOME (_, b) => b
    | NONE => false

  (* ---------------------------------------------------------------- *)
  (* truth tables / decision procedures                                *)

  (* enumerate all 2^k assignments; row r has bit (k-1-j) for variable j *)
  fun allAssignments names =
    let
      val k = List.length names
      fun pow2 0 = 1 | pow2 n = 2 * pow2 (n - 1)
      val total = pow2 k
      fun bitOf (r, j) =
        (r div (pow2 (k - 1 - j))) mod 2 = 1
      fun rowOf r =
        List.tabulate (k, fn j => (List.nth (names, j), bitOf (r, j)))
    in List.tabulate (total, rowOf) end

  fun truthTable p =
    let val names = vars p
    in List.map (fn row => (row, eval (envOf row) p)) (allAssignments names) end

  fun isTautology p = List.all (fn (_, v) => v) (truthTable p)
  fun isContradiction p = List.all (fn (_, v) => not v) (truthTable p)
  fun isSatisfiable p = List.exists (fn (_, v) => v) (truthTable p)

  fun equiv p q =
    let
      val names = List.foldl
                    (fn (x, a) => if List.exists (fn z => z = x) a then a else a @ [x])
                    [] (vars p @ vars q)
    in
      List.all (fn row => eval (envOf row) p = eval (envOf row) q)
               (allAssignments names)
    end

  (* ---------------------------------------------------------------- *)
  (* normal forms                                                      *)

  fun toNNF p =
    let
      fun nnf TrueP = TrueP
        | nnf FalseP = FalseP
        | nnf (Var s) = Var s
        | nnf (Not q) = nnfNot q
        | nnf (And (a, b)) = And (nnf a, nnf b)
        | nnf (Or (a, b)) = Or (nnf a, nnf b)
        | nnf (Imp (a, b)) = Or (nnfNot a, nnf b)
        | nnf (Iff (a, b)) =
            Or (And (nnf a, nnf b), And (nnfNot a, nnfNot b))
      and nnfNot TrueP = FalseP
        | nnfNot FalseP = TrueP
        | nnfNot (Var s) = Not (Var s)
        | nnfNot (Not q) = nnf q
        | nnfNot (And (a, b)) = Or (nnfNot a, nnfNot b)
        | nnfNot (Or (a, b)) = And (nnfNot a, nnfNot b)
        | nnfNot (Imp (a, b)) = And (nnf a, nnfNot b)
        | nnfNot (Iff (a, b)) =
            Or (And (nnf a, nnfNot b), And (nnfNot a, nnf b))
    in nnf p end

  fun toCNF p =
    let
      fun dist (And (a1, a2), b) = And (dist (a1, b), dist (a2, b))
        | dist (a, And (b1, b2)) = And (dist (a, b1), dist (a, b2))
        | dist (a, b) = Or (a, b)
      fun go (And (a, b)) = And (go a, go b)
        | go (Or (a, b)) = dist (go a, go b)
        | go q = q
    in go (toNNF p) end

  fun toDNF p =
    let
      fun dist (Or (a1, a2), b) = Or (dist (a1, b), dist (a2, b))
        | dist (a, Or (b1, b2)) = Or (dist (a, b1), dist (a, b2))
        | dist (a, b) = And (a, b)
      fun go (Or (a, b)) = Or (go a, go b)
        | go (And (a, b)) = dist (go a, go b)
        | go q = q
    in go (toNNF p) end
end

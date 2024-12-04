Control.Print.printDepth := 20;
Control.Print.printLength := 100;
CM.make "$smlnj-tdp/back-trace.cm";
SMLofNJ.Internals.TDP.mode := true;
exception InvalidEscapedCharacter of char;
exception MissingEscapedCharacter;
exception InvalidTokenStart of char;

datatype arith_expression =
   AE_NUM of int
 | AE_PLUS of arith_expression * arith_expression
 | AE_MINUS of arith_expression * arith_expression
 | AE_TIMES of arith_expression * arith_expression
 | AE_DIVIDE of arith_expression * arith_expression
;

fun arithInfixString(e : arith_expression) : string =
    case e of
      AE_NUM (n) => Int.toString n 
    | AE_PLUS (e1, e2) => "(" ^ arithInfixString e1 ^ " + " ^ arithInfixString e2 ^ ")"
    | AE_MINUS (e1, e2) => "(" ^ arithInfixString e1 ^ " - " ^ arithInfixString e2 ^ ")"
    | AE_TIMES (e1, e2) => "(" ^ arithInfixString e1 ^ " * " ^ arithInfixString e2 ^ ")"
    | AE_DIVIDE (e1, e2) => "(" ^ arithInfixString e1 ^ " / " ^ arithInfixString e2 ^ ")"
;

fun arithPrefixString(e: arith_expression) : string = 
  case e of
        AE_NUM (n) => Int.toString n 
      | AE_PLUS (e1, e2) => "(" ^ "+ " ^ arithPrefixString e1 ^ " " ^ arithPrefixString e2 ^ ")"
      | AE_MINUS (e1, e2) => "(" ^ "- " ^ arithPrefixString e1 ^ " " ^ arithPrefixString e2 ^ ")"
      | AE_TIMES (e1, e2) => "(" ^ "* " ^ arithPrefixString e1 ^ " " ^ arithPrefixString e2 ^ ")"
      | AE_DIVIDE (e1, e2) => "(" ^ "/ " ^ arithPrefixString e1 ^ " " ^ arithPrefixString e2 ^ ")"
;

fun evalArith(e: arith_expression) : int =
  case e of
        AE_NUM (n) => n 
      | AE_PLUS (e1, e2) => (evalArith) e1 + (evalArith e2) 
      | AE_MINUS (e1, e2) => (evalArith) e1 - (evalArith e2) 
      | AE_TIMES (e1, e2) => (evalArith) e1 * (evalArith e2) 
      | AE_DIVIDE (e1, e2) => (evalArith) e1 div (evalArith e2) 
;

datatype mixed_expression =
   ME_NUM of int
 | ME_PLUS of mixed_expression * mixed_expression
 | ME_TIMES of mixed_expression * mixed_expression
 | ME_LESSTHAN of mixed_expression * mixed_expression
;

datatype value =
   INT_VAL of int
 | BOOL_VAL of bool
 | ERROR_VAL
;

fun evalMixed(e: mixed_expression) : value =
 case e of
   ME_NUM (n) => INT_VAL n
 | ME_PLUS (e1, e2) => 
    let 
      val n1 = evalMixed e1
      val n2 = evalMixed e2
    in
      case (n1, n2) of 
        (INT_VAL n1, INT_VAL n2) => INT_VAL (n1 + n2)
        | ( _ , _) => ERROR_VAL
    end 
  
 | ME_TIMES (e1, e2) =>
    let 
      val n1 = evalMixed e1
      val n2 = evalMixed e2
    in
      case (n1, n2) of 
        (INT_VAL n1, INT_VAL n2) => INT_VAL (n1 * n2)
        | ( _ , _) => ERROR_VAL
    end 

 | ME_LESSTHAN (e1, e2) =>
    let 
      val n1 = evalMixed e1
      val n2 = evalMixed e2
    in
      case (n1, n2) of 
        (INT_VAL n1, INT_VAL n2) => BOOL_VAL (n1 < n2)
        | ( _ , _) => ERROR_VAL
    end 
;

datatype var_expression =
   VE_NUM of int
 | VE_ID of string
 | VE_PLUS of var_expression * var_expression
 | VE_TIMES of var_expression * var_expression
;

fun simplifyIdentities(e: var_expression) : var_expression =
  case e of 
    VE_NUM (n) => VE_NUM n
  | VE_ID (s) => VE_ID s
  | VE_PLUS (e1, e2) =>
    let
      val n1 = simplifyIdentities e1
      val n2 = simplifyIdentities e2
    in
      case (n1, n2) of
        ( _ , VE_NUM 0) => n1  (*First element is of VE_ID or VE_NUM*)
        | (VE_NUM 0, _ ) => n2 (*Second element is of VE_ID or VE_NUM*)
        | ( _ , _) => VE_PLUS (n1, n2) 
    end
  | VE_TIMES (e1, e2) =>
    let
      val n1 = simplifyIdentities e1
      val n2 = simplifyIdentities e2
    in
      case (n1, n2) of
        ( _ , VE_NUM 1) => n1  (*First element is of VE_ID or VE_NUM*)
        | (VE_NUM 1, _ ) => n2 (*Second element is of VE_ID or VE_NUM*)
        | ( _ , _) => VE_TIMES (n1, n2)
    end
;

fun foldConstants(e: var_expression) : var_expression = 
  case e of 
    VE_NUM (n) => VE_NUM n
  | VE_ID (s) => VE_ID s
  | VE_PLUS (e1, e2) =>
    let
      val n1 = foldConstants e1
      val n2 = foldConstants e2
    in
      case (n1, n2) of
        ( VE_NUM n1 , VE_NUM n2) => VE_NUM (n1 + n2)
        | ( _ , _ ) => VE_PLUS (n1, n2) (*Coverd strings + strings or strings + num *)
    end
  | VE_TIMES (e1, e2) =>
    let
      val n1 = foldConstants e1
      val n2 = foldConstants e2
    in
      case (n1, n2) of
        (VE_NUM n1, VE_NUM n2) => VE_NUM (n1 * n2)
        | ( _ , _ ) => VE_TIMES (n1, n2) (*Coverd strings * strings or strings * num *)
    end
;

datatype operator =
   OP_PLUS
 | OP_TIMES
;

datatype expression =
   NUM of int
 | ID of string
 | BINARY of {opr:operator, lft:expression, rht:expression}
 | FUNCTION of {parameter:string, body: expression}
 | CALL of {func:expression, argument:expression}
;

(*use @ to concatinate two lists together*)

fun gatherIdentifiers(e: expression) : string list =
  case e of 
    NUM (n) => []
    | ID (s) => [s]
    | BINARY {opr, lft, rht} => gatherIdentifiers (lft) @ gatherIdentifiers (rht)
    | FUNCTION {parameter = p, body = b} => p :: gatherIdentifiers (b)
    | CALL {func = f, argument = a} => gatherIdentifiers (f) @ gatherIdentifiers (a)
;

fun freeVariables(e: expression) : string list = 
  case e of 
    NUM (n) => []
    | ID (s) => [s]
    | BINARY {opr, lft, rht} => freeVariables (lft) @ freeVariables (rht)
    | FUNCTION {parameter = p, body = b} => List.filter (fn x => x <> p) (freeVariables(b))
    | CALL {func = f, argument = a} => freeVariables (f) @ freeVariables (a)

;

fun simpSubst (e1: expression) (s: string) (e2: expression) : expression =
  case e1 of 
    NUM (n) => NUM n
    | ID (x) => 
      if x = s
      then e2 
      else ID x
    | BINARY {opr, lft, rht} => BINARY {opr = opr, lft = (simpSubst lft s e2), rht = (simpSubst rht s e2)}
    | FUNCTION {parameter = p, body = b} => FUNCTION {parameter = p, body = (simpSubst b s e2)}
    | CALL {func = f, argument = a} => CALL {func = (simpSubst f s e2), argument = (simpSubst a s e2)}
;

fun betterSubst (e1: expression) (s: string) (e2: expression) : expression =
  case e1 of 
    NUM (n) => NUM n
    | ID (x) => 
      if x = s
      then e2 
      else ID x
    | BINARY {opr, lft, rht} => BINARY {opr = opr, lft = (betterSubst lft s e2), rht = (betterSubst rht s e2)}
    | FUNCTION {parameter = p, body = b} => 

      (*check for non-free variables in function; if p = s, anything inside the FUNC body shouldn't be replaced as it is bound to parameter*)
      if p = s
      then FUNCTION {parameter = p, body = b}
      else FUNCTION {parameter = p, body = (betterSubst b s e2)}
    | CALL {func = f, argument = a} => CALL {func = (betterSubst f s e2), argument = (betterSubst a s e2)}
;


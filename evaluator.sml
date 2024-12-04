Control.Print.printDepth := 20;
Control.Print.printLength := 100;
CM.make "$smlnj-tdp/back-trace.cm";
SMLofNJ.Internals.TDP.mode := true;
exception InvalidEscapedCharacter of char;
exception MissingEscapedCharacter;
exception InvalidTokenStart of char;
use "exceptions.sml";
open TextIO;

(*HashTable initialization*)
open HashTable;
exception CannotFindIt;
val hash_fn : string->word = HashString.hashString;
val cmp_fn : string*string->bool = (op =);
val initial_size : int = 101;

datatype value =
	  VAL_INT of int
    | VAL_BOOL of bool
    | VAL_STRING of string
    | VAL_CLOSURE of {id: unit ref, f: function, CE: state_type} (*{unit ref, function, state_type list}*) 
    | VAL_NONE
withtype state_type = (string, value) hash_table list; (*hash_table list*)


fun valType (v : value) : string = 
    case v of 
          VAL_INT n => "number"
        | VAL_BOOL b => "boolean"
        | VAL_STRING s => "string"
        | VAL_NONE => "none"
        | VAL_CLOSURE _ => "function"
;

fun evalEXP (state: state_type) (e: expression) : value = 
    case e of           
          EXP_NUM n => VAL_INT n
        | EXP_STRING s => VAL_STRING s
        | EXP_BOOL b => VAL_BOOL b
        | EXP_NONE => VAL_NONE
        | EXP_BINARY {opr = BOP_PLUS, lft, rht} =>
            (case (evalEXP state lft, evalEXP state rht) of 
                  (VAL_INT lval, VAL_INT rval) => VAL_INT (lval + rval)
                | (VAL_STRING s1, VAL_STRING s2) => VAL_STRING (s1 ^ s2)
                | (lval , rval) => raise AddException (valType lval, valType rval)         
            )
        | EXP_BINARY {opr = BOP_MINUS, lft, rht} =>
            (case (evalEXP state lft, evalEXP state rht) of 
                  (VAL_INT lval, VAL_INT rval) => VAL_INT (lval - rval)
                | (lval , rval) => raise ArithmeticException (BOP_MINUS, valType lval, valType rval)
            )
        
        | EXP_BINARY {opr = BOP_TIMES, lft, rht} =>
            (case (evalEXP state lft, evalEXP state rht) of 
                  (VAL_INT lval, VAL_INT rval) => VAL_INT (lval * rval)
                | (lval, rval ) => raise ArithmeticException (BOP_TIMES, valType lval, valType rval)
            )

        | EXP_BINARY {opr = BOP_DIVIDE, lft, rht} =>
            (case (evalEXP state lft, evalEXP state rht) of 
                  (VAL_INT lval, VAL_INT rval) => 
                    if rval = 0 
                    then raise ZeroDivideException
                    else VAL_INT (lval div (rval))
                | (lval, rval) => raise ArithmeticException (BOP_DIVIDE, valType lval, valType rval)
            )

        | EXP_BINARY {opr = BOP_MOD, lft, rht} =>
            (case (evalEXP state lft, evalEXP state rht) of 
                  (VAL_INT lval, VAL_INT rval) => 
                    if rval = 0 
                    then raise ZeroDivideException
                    else VAL_INT (lval mod (rval))
                | (lval, rval) => raise ArithmeticException (BOP_MOD, valType lval, valType rval)
            )

        | EXP_BINARY {opr = BOP_EQ, lft, rht} =>
            (case (evalEXP state lft, evalEXP state rht) of 
                  (VAL_INT lval, VAL_INT rval) => VAL_BOOL (lval = rval)
                | (VAL_BOOL lval, VAL_BOOL rval) => VAL_BOOL (lval = rval)
                | (VAL_STRING lval, VAL_STRING rval) => VAL_BOOL (lval = rval)
                | (VAL_CLOSURE {id = lID, f = lF, CE = lCE}, VAL_CLOSURE {id = rID, f = rF, CE = rCE}) => VAL_BOOL (lID = rID)
                | (VAL_NONE, VAL_NONE) => VAL_BOOL true
                | (lval, rval) => VAL_BOOL false
            )
        
        | EXP_BINARY {opr = BOP_NE, lft, rht} =>
            (case (evalEXP state lft, evalEXP state rht) of 
                  (VAL_INT lval, VAL_INT rval) => VAL_BOOL (lval <> rval)
                | (VAL_BOOL lval, VAL_BOOL rval) => VAL_BOOL (lval <> rval)
                | (VAL_STRING lval, VAL_STRING rval) => VAL_BOOL (lval <> rval)
                | (VAL_CLOSURE {id = lID, f = lF, CE = lCE}, VAL_CLOSURE {id = rID, f = rF, CE = rCE}) => VAL_BOOL (lID <> rID)
                | (VAL_NONE, VAL_NONE) => VAL_BOOL false
                | (lval, rval) => VAL_BOOL true
            )


        | EXP_BINARY {opr = BOP_LT, lft, rht} =>
            (case (evalEXP state lft, evalEXP state rht) of 
                  (VAL_INT lval, VAL_INT rval) => VAL_BOOL (lval < rval)
                | (lval, rval) => raise RelationalException (BOP_LT, valType lval, valType rval)
            )
        | EXP_BINARY {opr = BOP_GT, lft, rht} =>
            (case (evalEXP state lft, evalEXP state rht) of 
                  (VAL_INT lval, VAL_INT rval) => VAL_BOOL (lval > rval)
                | (lval, rval) => raise RelationalException (BOP_GT, valType lval, valType rval)
            )
        | EXP_BINARY {opr = BOP_LE, lft, rht} =>
            (case (evalEXP state lft, evalEXP state rht) of 
                  (VAL_INT lval, VAL_INT rval) => VAL_BOOL (lval <= rval)
                | (lval, rval) => raise RelationalException (BOP_LE, valType lval, valType rval)
            )
        | EXP_BINARY {opr = BOP_GE, lft, rht} =>
            (case (evalEXP state lft, evalEXP state rht) of 
                  (VAL_INT lval, VAL_INT rval) => VAL_BOOL (lval >= rval)
                | (lval, rval) => raise RelationalException (BOP_GE, valType lval, valType rval)
            )

        | EXP_BINARY {opr = BOP_AND, lft, rht} =>
            (case (evalEXP state lft) of 
                (VAL_BOOL lval) => 
                    if lval = false
                    then VAL_BOOL (false)
                    else
                        (case (evalEXP state rht) of
                            (VAL_BOOL rval) => 
                                if rval = false
                                then VAL_BOOL (rval)
                                else VAL_BOOL (true)
                            | (rval) => raise BooleanSecondException  (BOP_AND, valType rval)
                        )
                | (lval) => raise BooleanFirstException (BOP_AND, valType lval)
            )
        
        | EXP_BINARY {opr = BOP_OR, lft, rht} =>
            (case (evalEXP state lft) of 
                (VAL_BOOL lval) => 
                    if lval = true
                    then VAL_BOOL (true)
                    else
                        (case (evalEXP state rht) of
                            (VAL_BOOL rval) => 
                                if rval = true
                                then VAL_BOOL (true)
                                else VAL_BOOL (false)
                            | (rval) => raise BooleanSecondException  (BOP_OR, valType rval)
                        )
                | (lval) => raise BooleanFirstException (BOP_OR, valType lval)
            )
        
        | EXP_UNARY {opr = UOP_NOT, opnd} =>
            (case evalEXP state opnd of 
                (VAL_BOOL opVal) =>
                    if opVal = true
                    then VAL_BOOL false
                    else VAL_BOOL true
                | (opVal) => raise UnaryNotException (valType opVal) 
            )

        | EXP_UNARY {opr = UOP_MINUS, opnd} =>
            (case evalEXP state opnd of 
                (VAL_INT opVal) => VAL_INT(~opVal)
                | (opVal) => raise UnaryMinusException (valType opVal) 
            )
        
        | EXP_COND {guard, thenExp, elseExp} =>
            (case evalEXP state guard of
                VAL_BOOL gVal =>
                    if gVal = true
                    then evalEXP state thenExp
                    else evalEXP state elseExp
                | gVal => raise ConditionalException (valType gVal)
            )

        | EXP_ID k => 
            (case (searchStates state k) of 
                  SOME resState => lookup (resState) k 
                | NONE => raise UndeclaredVariableException k
            )

        | EXP_ASSIGN {lhs, rhs} =>
            (case (lhs, evalEXP state rhs) of
                (EXP_ID k, rval) => 
                    case (searchStates state k) of 
                          SOME resState => (insert (resState) (k, rval); rval)
                        | NONE => raise UndeclaredVariableAssignmentException k 
            )

        | EXP_CALL {func, args} =>
            let
                val closure = evalEXP state func; (*1*)
                val argList = evalArgs state args; (*2*)
                val argListSize = List.length argList;
            in
                (case closure of
                    VAL_CLOSURE {id, f = {params, decls, body}, CE} =>
                        let
                            val newTable = mkTable (hash_fn, cmp_fn) (initial_size, CannotFindIt) (*3*);
                            val newAE : state_type = newTable :: CE; (*5*)
                            val paramsSize = List.length params;

                        in
                            if argListSize > paramsSize
                            then raise CallTooManyArgumentsException 
                            else 
                                if argListSize < paramsSize
                                then raise CallTooFewArgumentsException 
                                else 
                                    (*4: bind the arguments to the parameters of the closure's anonymous function*)
                                    bindArgsParams newAE argList params;  
                                    evalKEYS newAE decls; (*3*)
                                    checkErrorRedeclaration (params) (decls); (*error handling*)
                                    helperSTMTS newAE body; (*6*)
                                    (case (find (hd newAE) "return") of (*newTable vs new AE*)
                                        SOME v => v
                                        | NONE => VAL_NONE
                                    )
                        end
                    | _ => raise NonFunctionException (valType closure)
                )
            end

        | EXP_ANON function => VAL_CLOSURE{id = ref(), f = function, CE = state} (* same structure as a call: code + storedEnv = closure, don't give it a name*)

and checkErrorRedeclaration (params: decl list) (decls: decl list): unit =
    (case params of 
        [] => ()
        | param::rest =>
            let
                val errorRedeclaration = List.exists (fn decl => decl = param) decls
            in 
                if errorRedeclaration = true
                then raise VariableRedeclarationException param
                else
                    checkErrorRedeclaration (rest) (decls)
            end
    )
    
and searchStates (CE_state: state_type) (key: string): (string, value) hash_table option =
    case CE_state of 
        [] => NONE
        | x::xs => (*CE_state :: rest of stateList*)
            (case (find x key) of
                SOME v => SOME(x)
                | NONE => searchStates xs key       
            ) 


and evalArgs (CE_state: state_type) (args: expression list): value list =
    case args of 
        [] => []
        | arg :: rest =>
            evalEXP CE_state arg :: evalArgs CE_state rest

and bindArgsParams (CE_state: state_type) (argList: value list) (params: decl list): unit = 
    case params of 
        [] => ()
        | param :: paramRest =>
            let 
                val arg = hd argList;
                val argRest = tl argList;
                val errorRedeclaration = List.exists (fn x => x = param) paramRest
            in
                if errorRedeclaration = true
                then raise VariableRedeclarationException param
                else
                    (insert (hd CE_state) (param, arg); bindArgsParams (CE_state) (argRest) (paramRest))
            end

and evalSTMT (state: state_type) (s: statement): unit = 
    case s of 
        ST_PRINT {exp} =>
            (case evalEXP state exp of 
                  VAL_INT n =>
                    if n < 0
                    then TextIO.output (TextIO.stdOut, "-" ^ Int.toString(~n))
                    else TextIO.output (TextIO.stdOut, Int.toString(n))
                | VAL_BOOL b => TextIO.output (TextIO.stdOut, Bool.toString b)
                | VAL_STRING s => TextIO.output (TextIO.stdOut, s)
                | VAL_NONE => TextIO.output (TextIO.stdOut, "none")
                | VAL_CLOSURE _ => TextIO.output (TextIO.stdOut, "function")
            )

        | ST_BLOCK {stmts} => helperSTMTS state stmts 
            
        | ST_IF {guard, th, el} =>
            (case evalEXP state guard of
                VAL_BOOL gVal =>
                    if gVal = true
                    then evalSTMT state th
                    else 
                        (case el of (*Check for SOME and NONE*)
                              SOME v => evalSTMT state v
                            | NONE => ()
                        )
                | gVal => raise IfGuardException (valType gVal)
            )

        | ST_WHILE {guard, body} =>
            let 
                val v = evalEXP state guard
            in
                (case v of 
                      VAL_BOOL gVal =>
                        if gVal = true
                        then 
                        (
                            evalSTMT state body; (*check if a return occurred*) 
                            (case (find (hd state) "return") of  (*return statement should stop the rest of the code from running*)
                                SOME v => ()
                                | NONE => evalSTMT state s
                            )
                        )
                        else ()
                    | gVal => raise WhileGuardException (valType gVal)
                )
            end

        | ST_EXP {exp} => ignore(evalEXP state exp)

        | ST_RETURN {exp} => 
            (case exp of 
                SOME returnVal => insert (hd state) ("return", (evalEXP state returnVal))
                | NONE => insert (hd state) ("return", VAL_NONE)
            )
            (*remove head of state to stop rest of code from running*)


and helperSTMTS (state: state_type) (L: statement list): unit =
    case L of
        [] => ()
        | x::xs => 
            (
                evalSTMT state x; (*check if a return occurred*)
                (case (find (hd state) "return") of  (*return statement should stop the rest of the code from running*)
                    SOME v => ()
                    | NONE => helperSTMTS state xs
                )
            )       
            
            

and helperTLE_Funcs (state: state_type) (L: (string * function) list): unit =
    case L of 
          [] => ()
        | x :: xs =>
            let
                val F = hd L
                val rest = tl L

            in
                (case (find (hd state) (#1F)) of 
                    SOME v => raise VariableRedeclarationException (#1F)
                    | NONE => 
                        (insert (hd state) (#1F, VAL_CLOSURE {id = ref(), f = #2F, CE = state}); 
                        helperTLE_Funcs state rest)
                )
            end    


and evalKEYS (CE_state: state_type) (L: string list): unit =
    case L of
        [] => ()
        | x::xs =>
            let
                val v = hd L;
                val rest = tl L;
                val errorRedeclaration = List.exists (fn x => x = v) rest
            in
                if errorRedeclaration = true
                then raise VariableRedeclarationException v
                else
                    insert (hd CE_state) (v, VAL_NONE);
                    evalKEYS CE_state rest
            end 

and checkReturnOutsideFunctionException(TLE_statements: statement list): unit =
    case TLE_statements of 
        [] => ()
        | x :: xs =>
            (case x of 
                ST_RETURN {exp} => raise ReturnOutsideFunctionException
                | _ => checkReturnOutsideFunctionException xs   
            )

and evaluate(p: program) : unit  = 
    let 
        val PROGRAM {decls, func_decls, stmts} = p;
        val keys = decls;
        val TLE_Funcs = func_decls;
        val TLE_statements = stmts;
        val TLE_state : state_type = [mkTable (hash_fn, cmp_fn) (initial_size, CannotFindIt)];
    in
        (checkReturnOutsideFunctionException TLE_statements; evalKEYS TLE_state keys; 
        helperTLE_Funcs TLE_state TLE_Funcs; helperSTMTS TLE_state TLE_statements)
    end
;
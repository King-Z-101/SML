Control.Print.printDepth := 20;
Control.Print.printLength := 100;
CM.make "$smlnj-tdp/back-trace.cm";
SMLofNJ.Internals.TDP.mode := true;
exception InvalidEscapedCharacter of char;
exception MissingEscapedCharacter;
exception InvalidTokenStart of char;

fun either (predicatePair: (('a -> bool) * ('a -> bool))) (value: 'a) : bool =
    let
        val first = #1 predicatePair
        val second = #2 predicatePair 
    in
        if first value
        then true
        else
            if second value
            then true
            else false
    end
;

fun satisfiesSome (predicateList: ('a -> bool) list, value : 'a) : bool = 
    case predicateList of
        [] => false
        | x::xs =>
            let
                val predicate = hd predicateList
                val tail = tl predicateList 
            in
                if predicate value
                then true 
                else satisfiesSome (tail, value)
            end
;

fun mapSome (f : ('a -> 'b option)) (input: 'a list) : 'b list =
    case input of
        [] => []
        | x::xs =>
            case f x of
                SOME res => res :: mapSome f xs 
                | NONE => mapSome f xs 
;

fun notIn(target : ''a, L: ''a list) : bool =
    let 
        val found = List.exists (fn e => e = target) L 
    in
        if found = true
        then false
        else true
    end

    (*
    case L of 
        [] => true
         | x::xs  => 
            if num = x
            then false
            else notIn(num, xs)
    *)
;

(*get value of key passed if exists*)
fun getByKey(key: ''a , input: (''a * 'b) list, default : 'b) : 'b =
	let
        val compareKey = fn (k,v) => k = key
    in
        case List.find compareKey input of
            SOME (k, v) => v
            | NONE => default
    end
;



datatype 'a List =
        ListNode of 'a * 'a List
      | EmptyList
;

fun lengthList(LL: 'a List) : int =
    case LL of
        EmptyList => 0
        | ListNode (hd, tail) =>
           1 + lengthList (tail) 
;

fun filterList(filter : ('a -> bool)) (LL: 'a List) : 'a List =
    case LL of
        EmptyList => EmptyList
        | ListNode (hd, tail) =>
            if filter hd = true 
            then ListNode(hd, filterList (filter) (tail))
            else filterList (filter) (tail)
;

datatype 'a VerboseTree =
        VerboseNode of {value: 'a, left: 'a VerboseTree, right: 'a VerboseTree}
      | Lefty of {value: 'a, left: 'a VerboseTree}
      | Righty of {value: 'a, right: 'a VerboseTree}
      | Leaf of {value: 'a}
      | EmptyVerboseTree 
;

fun sumTree(BT: int VerboseTree) : int =
    case BT of 
        EmptyVerboseTree => 0
        | Leaf {value = v} => v 
        | Righty {value = v, right} => v + sumTree(right)
        | Lefty {value = v, left} => v + sumTree(left)
        | VerboseNode {value = v, left = l, right = r} => v + sumTree(l) + sumTree(r)

;

(*use @ to concatinate two lists together*)

fun gatherTree(BT: 'a VerboseTree) : 'a list =
    case BT of 
        EmptyVerboseTree => []
        | Leaf {value = v} => [v] 
        | Righty {value = v, right} => v :: gatherTree(right)
        | Lefty {value = v, left} => v :: gatherTree(left)
        | VerboseNode {value = v, left = l, right = r} => v :: gatherTree(l) @ gatherTree(r)
;

datatype 'a BinaryTree =
        BinaryNode of {value: 'a, left: 'a BinaryTree, right: 'a BinaryTree}
      | EmptyBinaryTree
;

fun simplifyTree(N: 'a VerboseTree) : 'a BinaryTree = 
    case N of 
        EmptyVerboseTree => EmptyBinaryTree
        | Leaf {value = v} => BinaryNode{value = v, left = EmptyBinaryTree, right = EmptyBinaryTree} 
        | Righty {value = v, right} => BinaryNode{value = v, left = EmptyBinaryTree, right = simplifyTree(right)}
        | Lefty {value = v, left} => BinaryNode{value = v, left = simplifyTree(left), right = EmptyBinaryTree}
        | VerboseNode {value = v, left = l, right = r} => BinaryNode{value = v, left = simplifyTree(l), right = simplifyTree(r)}
;

Control.Print.printDepth := 20;
Control.Print.printLength := 100;
CM.make "$smlnj-tdp/back-trace.cm";
SMLofNJ.Internals.TDP.mode := true;
exception InvalidEscapedCharacter of char;
exception MissingEscapedCharacter;
exception InvalidTokenStart of char;

(*covert ints to strings*)
fun intToString (value : int) : string =
    if value < 0
    then 
        "-" ^ Int.toString(~value)
    else
        Int.toString(value)
;

(*return list of first elements in tuple list*)
fun firsts (pairs: ('a * 'b) list) : 'a list =
    case pairs of
		[] => []
		| (a,b) :: rest =>
			let 
				val result = firsts rest;
			in
				a :: result
			end
;

(*return list of first elements in tuple list*)

fun seconds (pairs: ('a * 'b) list) : 'b list = 
    case pairs of
		[] => []
		| (a,b) :: rest =>
			let 
				val result = seconds rest;
			in
				b :: result
			end
;

(*substitute first apperance of a #1 t with #2 t*)
fun replaceFirst(t: ''a * ''a * ''a list) : ''a list =
	case #3 t of 
		[] => []
		| head :: rest =>
			if head = #1 t
			then 
				#2 t :: rest
			else
				head :: replaceFirst(#1 t , #2 t , rest)

;

(*substitute all  apperances of a #1 t with #2 t*)
fun replaceAll(t: ''a * ''a * ''a list) : ''a list =
	case #3 t of 
		[] => []
		| head :: rest =>
			if head = #1 t
			then 
				#2 t :: replaceAll(#1 t , #2 t , rest)

			else
				head :: replaceAll(#1 t , #2 t , rest)

;

(*greater list refers to nums >= pivot*)

fun partition(t: int * int list) : int list * int list = 
	case #2 t of
		[] => ([], [])
		| head :: rest =>
			let
				val (less, greater) = partition(#1 t, rest)
			in 
				if head < #1 t
				then
					(head :: less, greater)
				else
					(less, head :: greater)
			end
;

(*get value of key passed if exists*)
fun getByKey(t: ''a * (''a * 'b) list * 'b) : 'b =
	case #2 t of
		[] => #3 t 
		| (k, v) :: rest =>
			if k = #1 t
			then
				v
			else
				getByKey(#1 t, rest, #3 t)
;

fun helper (L : char list) : char list = 
	case L of
		[] => []
	| #":" :: rest =>
		let
			val c = 
				if null rest
				then raise MissingEscapedCharacter
				else hd rest
			val tail = tl rest
		in
			case c of 
				#"n" => #"\n" :: helper(tail)
				| #"t" => #"\t" :: helper(tail)
				| #"\"" => #"\"" :: helper(tail)
				| #":" => #":" :: helper(tail)

				(*anything else*)
				| _ => raise InvalidEscapedCharacter c 
		end
	| c :: rest => c :: helper(rest)
;


fun convertEscapeSequences(value : string) : string =
	implode(helper(explode(value)))
;


(*creating python split()*)
fun helper (delim: char) (input: char list) (entry : string) : string list = 
	case input of
		[] => 
			if entry = ""
			then []
			else entry :: []
		| c :: rest =>
			if c = delim
			then
				if entry = ""
				then
					helper (delim) (rest) ("")
				else
					entry :: helper (delim) (rest) ("")
			else helper (delim) (rest) (entry ^ str(c))
;

fun split(pair: char * string) : string list =
	helper (#1 pair) (explode(#2 pair)) ("")
;

(*check if string starts with whitespace and if so build a string until non whitespace is detected*)
fun whitespaceHelper (prefix : string) (L : char list) : string * char list = 
	case L of 
		[] => (prefix, L)
		| c :: rest =>
			if Char.isSpace c
			then
				whitespaceHelper (prefix ^ str(c)) (rest)
			else
				(prefix, L)
;

fun whitespacePrefix(L: char list) : string * char list = 
	case L of 
		[] => ("", L)
		| c :: rest =>
			if Char.isSpace c
			then
				whitespaceHelper (str(c)) (rest)
			else
				("", L)
;

(*check if string starts with number and if so build a string until non number is detected*)
fun numberHelper (prefix : string) (L : char list) : string * char list = 
	case L of 
		[] => (prefix, L)
		| n :: rest =>
			if Char.isDigit n
			then
				numberHelper (prefix ^ str(n)) (rest)
			else
				(prefix, L)
;

fun numberPrefix(L: char list) : string * char list = 
	case L of 
		[] => ("", L)
		| c :: rest =>
			if Char.isDigit c
			then
				numberHelper (str(c)) (rest)
			else
				("", L)
;

(*check if string starts with letter and if so build a string until non alphaNum character is detected*)
fun identifierHelper (prefix : string) (L : char list) : string * char list = 
	case L of 
		[] => (prefix, L)
		| i :: rest =>
			if Char.isAlphaNum i
			then
				identifierHelper (prefix ^ str(i)) (rest) 
			else
				(prefix, L)
;

fun identifierPrefix(L: char list) : string * char list = 
	case L of 
		[] => ("", L)
		| head :: rest =>
			if Char.isAlpha head 
			then 
				identifierHelper ("" ^ str(head)) (rest)
			else
				("", L) 
;



(*
fun helper (L : char list) (entry : string) : char list = 
	let

	in

	end
; 
fun splitTokens(value: string) : string list = 
	let 
		val L = explode(value)
	in
		case L of
			[] => []
			| x :: xs => helper (L) ("")
	end 
;

*)

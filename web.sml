structure web :> web =
struct

open HolKernel Abbrev boolLib aiLib mlTreeNeuralNetwork
  mcts kernel human bloom exec rl;
val ERR = mk_HOL_ERR "web";

val main_tnn = read_tnn (selfdir ^ "/model/tnn83")
val main_iprogl = read_iprogl (selfdir ^ "/model/isol87")

(* -------------------------------------------------------------------------
   Escape uri
   ------------------------------------------------------------------------- *)

(* Copyright from https://github.com/kni/sml-uri/blob/master/uri-escape.sml *)
fun toHex1 i =
  if i >=  0 andalso i <=  9 then SOME (chr (i + 48)) else
  if i >= 10 andalso i <= 15 then SOME (chr (i + 55)) else
  NONE

fun fromHex1 c =
let
  val i = ord c
in
  if i >= 48 andalso i <=  57 then SOME (i - 48) else
  if i >= 97 andalso i <= 102 then SOME (i - 87) else
  if i >= 65 andalso i <=  70 then SOME (i - 55) else
  NONE
end

fun fromHex2 (h2, h1) =
  case fromHex1 h2 of NONE => NONE | SOME d2 =>
  case fromHex1 h1 of NONE => NONE | SOME d1 =>
  SOME (d2 * 16 + d1);

fun toHex2 d =
  if d < 0 orelse d >= 16 * 16 then NONE else
  SOME (valOf (toHex1 (d div 16)), valOf (toHex1 (d mod 16)));


fun isNotEscapedChar c = (* RFC3986 *)
  let
    val i = ord c
  in
    (i >= 65 andalso i <= 90)  (* A-Z *) orelse
    (i >= 97 andalso i <= 122) (* a-z *) orelse
    (i >= 48 andalso i <= 57)  (* 0-9 *) orelse
    c = #"-" orelse
    c = #"." orelse
    c = #"_" orelse
    c = #"~"
  end

fun escapeChar (c, r) = if isNotEscapedChar c then c::r else
  case toHex2 (ord c) of NONE => r | SOME (h2, h1) => (h1::(h2::(#"%"::r)));

fun escape text =
  String.implode (List.rev (CharVector.foldl escapeChar [] text))
(* end copyright *)

(* -------------------------------------------------------------------------
   Print iframe
   ------------------------------------------------------------------------- *)

val brython = "https://brython.info/tests/editor.html?code=";

fun print_iframe addr = print_endline (
  "<iframe name=\"pypres\" src =\"" ^ addr ^ 
  "\" width=\"95%\" height=\"400\"" ^
  "scrolling=\"yes\" style=\"margin:5px\" frameborder=\"1\">" ^
  "<p>Your user agent does not support iframes or is currently configured" ^
  " not to display iframes. However, you may visit" ^
  "<A href=\"" ^ addr ^ "\">the related document.</A></p></iframe>")

(* -------------------------------------------------------------------------
   Test if the input sequence is in the cache
   ------------------------------------------------------------------------- *)

fun is_prefix seq1 seq2 = case (seq1,seq2) of
    ([],_) => true
  | (_,[]) => false
  | (a1 :: m1, a2 :: m2) => if a1 = a2 then is_prefix m1 m2 else false

fun test_cache_one target (i,prog) = 
  let val seq = valOf (Array.sub(bloom.oseq,i)) in is_prefix target seq end

fun test_cache target = List.find (test_cache_one target) main_iprogl

(* -------------------------------------------------------------------------
   Generated sequence
   ------------------------------------------------------------------------- *)

fun gseq_result gseq =
  (
  print_endline ("Generated sequence:");
  print_endline (string_of_seq gseq)
  )

fun nmatch_seq (seq1,seq2) = case (seq1,seq2) of
    ([],_) => (0,true)
  | (_,[]) => (0,true)
  | (a1 :: m1, a2 :: m2) => 
    if a1 <> a2 then (0,false) else 
    let val (n,b) = nmatch_seq (m1,m2) in
      (n+1,b)
    end

fun find_largest a l = case l of
    [] => a
  | b :: m => if snd b > snd a then find_largest b m else find_largest a m

fun score_oeis gseq (anum,seq) = 
  let 
    val anumr = Real.fromInt anum / 10000000.0
    fun scoref (matchn,contb,shiftn) =
      Real.fromInt matchn * Math.pow (0.95, Real.fromInt shiftn) 
      * (if contb then 1.0 else 0.5) - anumr
    fun loop shiftn n cseq = 
      if null cseq orelse shiftn >= n then [] else
      let val (matchn,contb) = nmatch_seq (gseq,cseq) in
        ((matchn,contb,shiftn,anum), scoref (matchn,contb,shiftn))
        :: loop (shiftn + 1) n (tl cseq)
      end
    val l = loop 0 3 seq
  in    
    if null l then NONE else SOME (find_largest (hd l) (tl l))
  end

fun print_oeis (matchn,contb,shiftn,anum) =
  let val anums =  "A" ^ its anum in
    "<a href=https://oeis.org/search?q=" ^ anums ^ ">" ^ anums ^ "</a>" ^
    "(" ^ its shiftn ^ "-" ^ its (shiftn + matchn) ^ ")"
  end

fun oeis_result gseq =
  let 
    val l1 = List.mapPartial (score_oeis gseq) oseql
    val l2 = map fst (first_n 3 (dict_sort compare_rmax l1))
  in      
    print_endline ("Matches best with: " ^ 
    String.concatWith ", " (map print_oeis l2)) 
  end

(* -------------------------------------------------------------------------
   Generated program
   ------------------------------------------------------------------------- *)

fun prog_result (p,to) =
  let val s = case to of 
      NONE => "in cache:"
    | SOME t => "during search in " ^ rts_round 2 t ^ " seconds:"
  in
    print_endline ("Program found " ^ s);
    print_endline ("f(x) := " ^ humanf p)
  end

fun python_result gseq p =
  let 
    val code = human_python (length gseq) p 
    val address = brython ^ (escape code)
  in
    print_endline ("Execute the equivalent Python program " ^
                   "<a href=\"" ^ address ^ "\">here</a>:");
    print_endline "";
    print_iframe address
  end

(* -------------------------------------------------------------------------
   Main function
   ------------------------------------------------------------------------- *)

fun parse_seq s = map Arbint.fromString 
  (String.tokens (fn x => mem x [#",",#"\n",#" ",#"\t",#"\r"]) s)

fun web_result n (po,to) = case (po,to) of
    (NONE,NONE) => 
      (
      print_endline "Unexpected error";
      app print_endline (List.tabulate (8,fn _ => ""))  
      )
  | (NONE, SOME t) => 
      (
      print_endline ("Could not find a program for the given sequence in " ^
      rts_round 2 t ^ " seconds:");
      app print_endline (List.tabulate (8,fn _ => ""))        
      )
  | (SOME p, to) => 
    let val gseq = penum p n handle NotFound => [] in
      gseq_result gseq;
      oeis_result gseq;
      prog_result (p,to);
      python_result gseq p
    end

fun web tim n targets = 
  let 
    val _ = game.time_opt := SOME tim
    val target = parse_seq targets
    val l = filter (test_cache_one target) main_iprogl
    val po =
      if null l then 
        let val (po,t) = add_time (search_target main_tnn) target in
          (po, SOME t)
        end
      else (SOME (hd (dict_sort prog_compare_size (map snd l))), NONE)
  in
    web_result n po
  end


end (* struct *)

(* -------------------------------------------------------------------------
   Test web interface
   ------------------------------------------------------------------------- 

load "web"; open aiLib game human exec rl web;
web 10.0 32 "2 3 5 7 11 13 17 19 23 29";
*)





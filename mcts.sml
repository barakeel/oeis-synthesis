structure mcts :> mcts =
struct

open HolKernel Abbrev boolLib aiLib

val ERR = mk_HOL_ERR "mcts"

(* -------------------------------------------------------------------------
   Search tree
   ------------------------------------------------------------------------- *)

type 'a node = {board : 'a, sum : real, vis : real}
datatype ('a,'b) tree =
  Leaf | Node of 'a node * ('b * real * ('a,'b) tree) vector
fun dest_node x = case x of Node y => y | _ => raise ERR "dest_node" ""
fun is_node x = case x of Node y => true | _ => false
fun is_leaf x = case x of Leaf => true | _ => false

(* -------------------------------------------------------------------------
   MCTS specification
   ------------------------------------------------------------------------- *)

type ('a,'b) game =
  {
  apply_move : 'b -> 'a -> 'a,
  available_movel : 'a -> 'b list,
  string_of_board : 'a -> string,
  string_of_move : 'b -> string,
  board_compare : 'a * 'a -> order,
  move_compare : 'b * 'b -> order,
  movel : 'b list
  }

fun uniform_player game board =
  (0.0, map (fn x => (x,1.0)) (#available_movel game board))

fun random_player game board =
  (random_real (), map (fn x => (x,1.0)) (#available_movel game board))

type ('a,'b) player = 'a -> real * ('b * real) list

type mctsparam =
  {
  time : real option, nsim : int option,
  explo_coeff : real,
  noise : bool, noise_coeff : real, noise_gen : unit -> real
  }

type ('a,'b) mctsobj =
  {mctsparam : mctsparam, game : ('a,'b) game, player : ('a,'b) player}

(* --------------------------------------------------------------------------
   Policy noise
   ------------------------------------------------------------------------- *)

fun normalize_prepol prepol =
  let val (l1,l2) = split prepol in combine (l1, normalize_proba l2) end

fun add_noise param prepol =
  let
    val noisel1 = List.tabulate (length prepol, fn _ => (#noise_gen param) ())
    val noisel2 = normalize_proba noisel1
    fun f ((move,polv),noise) =
      let
        val coeff = #noise_coeff param
        val newpolv = (1.0 - coeff) * polv + coeff * noise
      in
        (move,newpolv)
      end
  in
    map f (combine (prepol,noisel2))
  end

(* -------------------------------------------------------------------------
   Creation of a node
   ------------------------------------------------------------------------- *)

fun create_node obj board =
  let
    val game = #game obj
    val param = #mctsparam obj
    val (value,pol1) = (#player obj) board
    val pol2 = normalize_prepol pol1
    val pol3 = if #noise param then add_noise param pol2 else pol2
  in
    (Node ({board=board,sum=value,vis=1.0},
            Vector.fromList (map (fn (a,b) => (a,b,Leaf)) pol3)),
     value)
  end

fun starting_tree obj board = fst (create_node obj board)

(* -------------------------------------------------------------------------
   Score of a choice in a policy according to pUCT formula.
   ------------------------------------------------------------------------- *)

fun score_puct param sqvtot (move,polv,ctree) =
  let
    val (sum,vis) = case ctree of
      Leaf => (0.0,0.0)
    | Node (cnode,_) => (#sum cnode, #vis cnode)
  in
    (sum + #explo_coeff param * polv * sqvtot) / (vis + 1.0)
  end

(* -------------------------------------------------------------------------
   Selection of a node to extend by traversing the tree.
   ------------------------------------------------------------------------- *)

fun rebuild_tree reward buildl tree = case buildl of
    [] => tree
  | build :: m => rebuild_tree reward m (build reward tree)

fun select_child obj buildl (node,cv) =
  let
    val param = #mctsparam obj
    fun update_node reward {board,sum,vis} =
      {board=board, sum=sum+reward, vis=vis+1.0}     
  in
    let
      val _ = if Vector.length cv = 0
        then raise ERR "no move available" "" else ()
      val scoref = score_puct param (Math.sqrt (#vis node))
      val ci = vector_maxi scoref cv
      val (cmove,cpol,ctree) = Vector.sub (cv,ci)
      fun build reward cfuture =
        let val ctreev = Vector.update (cv,ci,(cmove,cpol,cfuture)) in
          Node (update_node reward node,ctreev)
        end
      val newbuildl = build :: buildl
    in
      case ctree of
        Leaf =>
        let
          val newboard = (#apply_move (#game obj)) cmove (#board node)
          val (newctree,reward) = create_node obj newboard
        in
          rebuild_tree reward newbuildl newctree
        end
      | Node x => select_child obj newbuildl x
    end
  end

(* -------------------------------------------------------------------------
   MCTS
   ------------------------------------------------------------------------- *)

fun mk_timer param =
  if isSome (#nsim param) then
    let val threshold = valOf (#nsim param) in
      fn n => (Real.round n) >= threshold
    end
  else if isSome (#time param) then
    let
      val timer = Timer.startRealTimer ()
      val limit = Time.fromReal (valOf (#time param))
    in
      fn _ => Timer.checkRealTimer timer > limit
    end
  else (fn _ => false)

fun mcts obj starttree =
  let
    val timerf = mk_timer (#mctsparam obj)
    fun loop n tree =
      if timerf (#vis (fst (dest_node tree))) then tree else
      loop (n+1) (select_child obj [] (dest_node tree))
  in
    loop 0 starttree
  end

(* -------------------------------------------------------------------------
   Statistics
   ------------------------------------------------------------------------- *)

fun tree_size tree = case tree of
    Leaf => 0
  | Node (node,ctreev) => 1 + 
     sum_int (map (tree_size o #3) (vector_to_list ctreev))

fun score_visit (move,polv,ctree) = case ctree of
      Leaf => 0.0
    | Node (cnode,_) => (#vis cnode)

fun most_visited_path tree = case tree of
    Leaf => []
  | Node (node,cv) =>
    if Vector.length cv = 0 then [(node,NONE)] else
    let
      val ci = vector_maxi score_visit cv
      val (cmove,_,ctree) = Vector.sub (cv,ci)
    in
      (node, SOME cmove) :: most_visited_path ctree
    end


end (* struct *)

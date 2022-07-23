signature mcts =
sig

  include Abbrev

  (* search tree: 'a is a board position, 'b is a move *)
  type 'a node = {board : 'a, sum : real, vis : real}
  datatype ('a,'b) tree =
    Leaf | Node of 'a node * ('b * real * ('a,'b) tree) vector
  val dest_node : ('a,'b) tree -> 'a node * ('b * real * ('a,'b) tree) vector
  val is_node : ('a,'b) tree -> bool
  val is_leaf : ('a,'b) tree -> bool

  (* MCTS specification *)
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

  type ('a,'b) player = 'a -> real * ('b * real) list
  val uniform_player : ('a,'b) game -> ('a,'b) player
  val random_player : ('a,'b) game -> ('a,'b) player

  type mctsparam =
    {time : real option, nsim : int option,
     explo_coeff : real,
     noise : bool, noise_coeff : real, noise_gen : unit -> real}

  type ('a,'b) mctsobj =
    {mctsparam : mctsparam, game : ('a,'b) game, player : ('a,'b) player}

  (* MCTS search function *)
  val starting_tree : ('a,'b) mctsobj -> 'a -> ('a,'b) tree
  val mcts : ('a,'b) mctsobj -> ('a,'b) tree -> ('a,'b) tree

  (* Statistics *)
  val most_visited_path : ('a,'b) tree -> ('a node * 'b option) list
  val tree_size : ('a,'b) tree -> int


end

signature qprove = sig

  type prog = kernel.prog
  type record = {intl : int list, terml: prog list, thml: prog list};
  type exec = record * record -> record
  
  val empty_record : record
  
  val execv : (exec list -> exec) vector
  val mk_exec : prog -> exec
  
  val string_to_term : string -> prog
  val term_to_string : prog -> string
  
  val init_conjecture : prog -> record
  
end

signature tptp =
sig

  include Abbrev

  val axl : term list
  val mk_cj : int list -> term

end

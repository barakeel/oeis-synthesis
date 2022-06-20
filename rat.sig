signature rat =
sig

  type rat = (Arbint.int * Arbint.int)
  val large_rarb : rat -> bool
  val large_rint : rat -> bool
  val rzero : rat
  val rone : rat
  val rtwo : rat
  val rmult : rat * rat -> rat
  val raddi : rat * rat -> rat
  val rdiff : rat * rat -> rat   
  val rmodu : rat * rat -> rat
  val rcond : rat * rat * rat -> rat
  val rcondeq : rat * rat * rat -> rat
  val rdivi : rat * rat -> rat
  val rdivr : rat * rat -> rat
  val rintpart : rat -> rat
  val rnumer : rat -> rat
  val rdenom : rat -> rat 
  val is_rint : rat -> bool
  val intpart : rat -> Arbint.int
  val mk_rat : Arbint.int -> rat

end

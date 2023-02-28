signature json = sig

    datatype json = OBJECT of (string * json) list
                  | ARRAY of json list
                  | NUMBER of real
                  | STRING of string
                  | BOOL of bool
                  | NULL

    datatype 'a result = OK of 'a
                       | ERROR of string

    val parse : string -> json result
    val serialise : json -> string
    val serialiseIndented : json -> string

end

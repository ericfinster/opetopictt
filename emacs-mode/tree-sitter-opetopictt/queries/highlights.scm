; Keywords


"def"  @keyword
"import" @keyword
"module" @keyword
"where" @keyword
"end" @keyword

"let"  @keyword
"in"   @keyword

":" @punctuation
"=" @punctuation
"(" @punctuation
")" @punctuation
"," @punctuation

"[" @punctuation.special
"]" @punctuation.special
"{" @punctuation.special
"}" @punctuation.special
"|" @punctuation.special
"@" @punctuation.special

"lf" @label
"nd" @label
"tt" @label

"U"   @constant
"fst" @constant
"snd" @constant

(var_declaration
 variable: (identifier) @variable)

(module_entry
  name: (module_name) @label)

(def_entry
  name: (identifier) @function)

((identifier) @function
 (#is-not? local))

(comment) @comment




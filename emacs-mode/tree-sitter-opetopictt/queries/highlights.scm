; Keywords


"def"  @keyword
"normalize" @keyword
"expand" @keyword
"import" @keyword

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
"⊢" @punctuation.special
"@" @punctuation.special

"lf" @label
"nd" @label
"tt" @label

"U"   @constant
"fst" @constant
"snd" @constant

(var_declaration
 variable: (identifier) @variable)

(def_command
 name: (identifier) @function)

((identifier) @function
 (#is-not? local))

(comment) @comment




; Keywords


"let"  @keyword
"normalize" @keyword
"expand" @keyword
"comp" @keyword
"fill" @keyword
"compu" @keyword
"fillu" @keyword

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
"●" @punctuation.special

"lf" @label
"nd" @label
"tt" @label

"U"   @constant
"fst" @constant
"snd" @constant

(var_declaration
 variable: (identifier) @variable)

(let_command
 name: (identifier) @function)

((identifier) @function
 (#is-not? local))

(comment) @comment



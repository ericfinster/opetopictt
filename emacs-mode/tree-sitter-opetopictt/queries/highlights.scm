; Keywords


"def"  @keyword
"import" @keyword
"module" @keyword
"where" @keyword
"end" @keyword
"shape" @keyword

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

(def_entry name: (identifier) @function)
(module_entry name: (module_name) @label)
(import_stmt name: (identifier) @label)
(shape_entry name: (identifier) @function)

(app . (expression (identifier) @function))

(qname) @function
(identifier) @variable
(comment) @comment




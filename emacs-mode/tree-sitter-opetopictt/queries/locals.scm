; locals

(let_command) @local.scope
(pi_type) @local.scope
(sig_type) @local.scope

(var_declaration
 variable: (identifier) @local.definition) 

(identifier) @local.reference

module.exports = grammar({
    name: 'opetopictt',

    extras: $ => [
	$.comment,
	/[\s]/
    ],

    rules: {
	
	source_file: $ => seq(
	    repeat($.import_stmt),
	    repeat($._command)
	),

	comment: $ => token(seq(
	    '#', /.*/
	)),

	//
	//  Imports
	//

	import_stmt: $ => seq(
	    'import',
	    field("name", $.identifier)
	),
	
	//
	//  Commands 
	//
	
	_command: $ => choice(
	    $.def_command,
	    $.normalize_command,
	    $.expand_command
	),

	def_command: $ => seq(
	    'def',
	    field("name", $.identifier),
	    field("context", optional($.telescope)),	    
	    ':',
	    field("type", $.expression), 
	    '=',
	    field("body", $.expression)
	),

	normalize_command: $ => seq(
	    'normalize',
	    field("context", optional($.telescope)),	    
	    ':',
	    field("type", $.expression), 
	    '\u{22a2}',
	    field("term", $.expression)
	),

	ident_pd: $ => choice(
	    'tt',
	    seq('{',$.identifier,'}'),
	    seq('lf',$.ident_pd),
	    seq('nd',$.ident_pd,$.ident_pd),
	    seq('(',$.ident_pd,')')
	),

	opetope: $ => sepSeq1('|',$.ident_pd),
	
	expand_command: $ => seq(
	    'expand',
	    field("context", optional($.telescope)),	    
	    ':',
	    field("type", $.expression), 
	    '|',
	    field("term", $.expression),
	    '|',
	    $.opetope
	),

	//
	//  Expressions 
	// 
	
	var_declaration: $ => choice(
	    seq('(', field("variable",$.identifier), ':', field("type",$.expression), ')')
	),

	telescope: $ => repeat1($.var_declaration),

	pi_head: $ => choice(
	    $.var_declaration,
	    $.expression
	),

	pi_type: $ => prec(2, seq($.pi_head,$.times,$.expression)),
	sig_type: $ => prec(2, seq($.pi_head,$.arrow,$.expression)),
	
	expression: $ => choice(

	    prec.right(1, seq($.expression,',',$.expression)),
	    prec.right(1, seq('let',$.identifier,':',$.expression,
		  	'=',$.expression,'in',$.expression)),
	    
	    prec(2, seq($.lambda,$.identifier,'.',$.expression)),
	    $.pi_type,
	    $.sig_type,
	    
	    prec.left(3,seq($.expression, $.expression)),
	    
	    prec(4, 'U'),
	    prec(4, $.identifier),
	    prec(4, seq('(',$.expression,')')),
	    prec(4, seq('fst',$.expression)),
	    prec(4, seq('snd',$.expression)),
	    prec(4, seq('[',$.expression,'@',$.opetope,']'))
	    
	),

	// expr: $ => choice(
	//     $.expr1,
	//     $.expr1,',',$.expr
	// ),

	// expr1: $ => choice(
	//     $.expr2, 
	//     seq($.lambda,$.identifier,'.',$.expr1),
	//     seq($.pi_head,$.arrow,$.expr1),
	//     seq($.pi_head,$.times,$.expr1)
	// ),

	// expr2: $ => choice(
	//     $.expr3,
	//     seq($.expr2,$.expr3)
	// ),
	
	// expr3: $ => choice(
	//     'U',
	//     $.identifier,
	//     seq('(',$.expr,')'),
	//     seq('fst',$.expr3),
	//     seq('snd',$.expr3),
	//     seq('[',$.expr,'@',$.opetope,']')
	// ),

	
	//
	//  Lexical definitions 
	//
	
	lambda: $ => token(choice('\\', '\u{03BB}')),
	arrow: $ => token(choice('->', '\u{2192}')),
	times: $ => '\u{d7}',
	
	identifier: $ => {

	    const digit = /[0-9]/
	    const lower_case = /[a-z]/;
	    const upper_case = /[A-Z]/;
	    const greek_lower = /[\u{03B1}-\u{03BA}|\u{03BC}-\u{03C9}]/u;
	    const greek_upper = /[\u{0391}-\u{03A9}]/u; 
	    const subscript = /[\u{2080}-\u{208E}|\u{2090}-\u{209C}]/u;
	    		  
	    const letter = choice(
		lower_case,
		upper_case,
		greek_lower,
		greek_upper
	    );

	    return token(seq(
		letter,
		repeat(choice(
		    letter,
		    subscript,
		    '_', '-', digit
		))))

	    
	}
	
    }

});


function sepSeq1(sep,rule) {
    return seq(rule, repeat(seq(sep, rule)));
}

function sepSeq(sep,rule) {
    return optional(sepSeq1(sep,rule));
}

//
//  grammar.js - tree sitter grammar for opetopictt

const digit = /[0-9]/
const lower_case = /[a-z]/;
const upper_case = /[A-Z]/;
const greek_lower = /[\u{03B1}-\u{03BA}|\u{03BC}-\u{03C9}]/u;
const greek_upper = /[\u{0391}-\u{03A9}]/u; 
const subscript = /[\u{2080}-\u{208E}|\u{2090}-\u{209C}]/u;

const roman_letter = choice(
    lower_case,
    upper_case,
)

const letter = choice(
    roman_letter,
    greek_lower,
    greek_upper
);

module.exports = grammar({
    name: 'opetopictt',

    extras: $ => [
	$.comment,
	/[\s]/
    ],

    rules: {
	
	source_file: $ => seq(
	    repeat($.import_stmt),
	    repeat($._entry)
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
	//  Top Level Structure
	//
	
	_entry: $ => choice(
	    $.def_entry,
	    $.module_entry,
	    $.shape_entry
	),

	def_entry: $ => seq(
	    'def',
	    field("name", $.identifier),
	    field("context", optional($.telescope)),	    
	    ':',
	    field("type", $.expression), 
	    '=',
	    field("body", $.expression)
	),

	module_entry: $ => seq(
	    'module',
	    field("name",$.module_name),
	    field("context", optional($.telescope)),
	    'where',
	    field("entries",repeat($._entry)),
	    'end'
	),

	shape_entry: $ => seq(
	    'shape',
	    field("name",$.identifier),
	    "=",
	    field("shape",$.opetope)
	), 

	//
	//  Opetopes
	//

	ident_pd: $ => choice(
	    'tt',
	    seq('{',$.identifier,'}'),
	    seq('lf',$.ident_pd),
	    seq('nd',$.ident_pd,$.ident_pd),
	    seq('(',$.ident_pd,')')
	),

	opetope: $ => sepSeq1('|',$.ident_pd),
	
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

	pair: $ => prec.right(1,seq($.expression,',',$.expression)),
	
	let_expr: $ => prec.right(1, seq('let',$.identifier,':',$.expression,
		  			 '=',$.expression,'in',$.expression)),

	lam: $ => prec(2, seq($.lambda,$.identifier,$.arrow,$.expression)), 
	app: $ => prec.left(3,seq($.expression, $.expression)), 

	fst: $ => prec(4, seq('fst',$.expression)),
	snd: $ => prec(4, seq('snd',$.expression)),
	refl: $ => prec(4,choice(
	    seq('[',$.expression,'@',$.identifier,']'),
	    seq('[',$.expression,'@',$.opetope,']'))),
	
	expression: $ => choice(

	    $.pair,
	    $.let_expr,
	    
	    $.lam,
	    $.pi_type,
	    $.sig_type,
	    
	    $.app,
	    
	    prec(4, 'U'),
	    prec(4, $.identifier),
	    prec(4, $.qname),
	    prec(4, seq('(',$.expression,')')),
	    $.fst,
	    $.snd,
	    $.refl
	    
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

	module_name: $ => seq(
	    upper_case,
	    repeat(roman_letter)
	),

	identifier: $ => token(seq(
	    letter,
	    repeat(choice(
		letter,
		subscript,
		'_', '-', digit
	    )))),

	// qname_id: $ => token.immediate(seq(
	//     letter,
	//     repeat(choice(
	// 	letter,
	// 	subscript,
	// 	'_', '-', digit
	//     )))), 

	// qual_name: $ => seq(
	//     repeat(seq(
	// 	$.module_name,
	// 	token.immediate('.')
	//     )),
	//     $.qname_id
	// ),
	
	qname: $ => token(seq(
	    repeat1(seq(alias(seq(
		upper_case,
		repeat(roman_letter)), $.module_name),'.')),
	    
	    seq(letter,
		repeat(choice(
		    letter,
		    subscript,
		    '_', '-', digit
		)))))
	
    }

});


function sepSeq1(sep,rule) {
    return seq(rule, repeat(seq(sep, rule)));
}

function sepSeq(sep,rule) {
    return optional(sepSeq1(sep,rule));
}

module.exports = grammar({
    name: 'opetopictt',

    extras: $ => [
	$.comment,
	/[\s]/
    ],

    rules: {
	
	source_file: $ => repeat($._command),

	comment: $ => token(seq(
	    '#', /.*/
	)),
	
	//
	//  Commands 
	//
	
	_command: $ => choice(
	    $.let_command
	),

	let_command: $ => seq(
	    'let',
	    field("name", $.identifier),
	    field("context", optional($.telescope)),	    
	    ':',
	    field("type", $.expression), 
	    '=',
	    field("body", $.expression)
	),

	//
	//  Expressions 
	// 
	
	var_declaration: $ => choice(
	    seq('(', $.identifier, ':', $.expression, ')')
	),

	telescope: $ => repeat1($.var_declaration),

	pi_head: $ => choice(
	    $.var_declaration,
	    $.expression
	),

	term_seq: $ => seq(
	    sepSeq(';',$.expression),
	    '\u{22a2}',
	    choice(
		'\u{25cf}',
		$.expression
	    )
	),

	tr_expr: $ => choice(
	    'tt',
	    seq('{',$.term_seq,'}'),
	    seq('lf',$.tr_expr),
	    seq('nd',$.tr_expr,$.tr_expr),
	    seq('(',$.tr_expr,')')
	),

	cmplx: $ => sepSeq1('|',$.tr_expr),

	cell_config: $ => seq(
	    '[',optional($.telescope),'\u{22a2}',$.expression,'|',$.cmplx,']'
	),
	
	expression: $ => choice(
	    
	    prec(1, seq($.lambda,$.identifier,'.',$.expression)),
	    prec(1, seq($.lambda,'{',$.identifier,'}',$.expression)),
	    prec(1, seq($.pi_head,$.arrow,$.expression)),
	    
	    prec.left(2,seq($.expression, $.expression)),
	    
	    prec(3, 'U'),
	    prec(3, $.identifier),
	    prec(3, seq('(',$.expression,')')),
	    prec(3, $.cell_config),
	    prec(3, seq('comp',$.cell_config)),
	    prec(3, seq('fill',$.cell_config))
	    
	),
	
	//
	//  Lexical definitions 
	//
	
	lambda: $ => token(choice('\\', '\u{03BB}')),
	arrow: $ => token(choice('->', '\u{2192}')),
	
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



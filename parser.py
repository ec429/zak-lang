#!/usr/bin/python

import re, sys, pprint
from pyparsing import *

## Parser

# declarations grammar TODO
"""
<declaration>   ::= <object-decls> ';' | <function-defn>
<array-decl>    ::= <direct-decl> '[' <expression> ']'
<abs-arr-decl>  ::= <dir-abs-decl>? '[' <expression> ']'
<type-name>     ::= <type> <abstract-decl>
"""

# expressions grammar TODO
"""
<compound-lit>  ::= '(' <type-name> ')' '{' <initialiser-list> ','? '}'
"""

# statements grammar TODO
"""
<function-defn> ::= <regparm>? <identifier> '(' <param-types> ')' <block-stmt>
<block-stmt>    ::= '{' <declare-list>? <stmt-list>? '}'
<declare-list>  ::= <declare> <declare-list>?
<stmt-list>     ::= <statement> <stmt-list>?
<statement>     ::= <expr-stmt> | <if-stmt> | <goto-stmt> | <label-stmt> |
                    <return-stmt> | <block-stmt>
<expr-stmt>     ::= <expression> ';'
<if-stmt>       ::= 'if' '(' <expression> ')' <statement> <else-clause>?
<else-clause>   ::= 'else' <statement>
<goto-stmt>     ::= 'goto' <label> ';'
<label>         ::= <identifier>
<label-stmt>    ::= <label> ':'
<return-stmt>   ::= 'return' <expression>? ';'
"""

def OGroup(token, name):
    return Optional(Group(token).setResultsName(name).setName(name))
def Alternate(l):
    if isinstance(l, dict):
        l = l.iteritems()
    return MatchFirst(Group(t).setResultsName(n).setName(n) for (n,t) in l)
def Alternate2(p, l):
    return p | Alternate(l)
def Alternate2R(p, l):
    return Alternate(l) | p
def Alternate3(p, q, n):
    return p | Group(q).setResultsName(n).setName(n)
def Litor(*args):
    return MatchFirst(Literal(s) for s in args)
def Keyor(*args):
    return MatchFirst(Keyword(s) for s in args)

class Parser(object):
    identifier = Word(alphas + '_', alphanums + '_')
    qualifier = Keyor('const', 'volatile')
    storage_class = Keyor('auto', 'static', 'extern')
    ty_pe = MatchFirst([Keyword('void'), Keyword('bool'), Keyword('byte'),
                        Keyword('word'), Keyword('struct') + identifier("stag"),
                        Keyword('enum') + identifier("etag")])
    qualifier_list = OneOrMore(qualifier)
    pointer = Forward()
    pointer <<= Group(Literal('*') + OGroup(qualifier_list, "qualifier_list") +
                      OGroup(pointer, "pointer"))
    flag_name = Literal('S') | Literal('Z') | Literal('H') |\
                Literal('P') | Literal('N') | Literal('C')
    flag_ident = (Suppress(Literal('#')) + flag_name)
    reg8 = Litor('A', 'B', 'C', 'D', 'E', 'H', 'L', 'IXH', 'IXL', 'IYH', 'IYL')
    reg16 = Litor('BC', 'DE', 'HL', 'IX', 'IY')
    regf = Optional(Literal('!'))("not") + flag_ident
    register = Alternate({'reg8': reg8, 'reg16': reg16, 'regf': regf})
    regparm = Suppress(Literal('@')) + register
    decl_spec = Forward()
    array_decl = NoMatch() # TODO
    abstract_decl = Forward()
    dir_abs_decl = Forward()
    abs_arr_decl = NoMatch() # TODO
    param_types = Forward()
    dir_abs_decl_no_func = Alternate2(Suppress(Literal('(')) + abstract_decl +
                                      Suppress(Literal(')')),
                                      {'abs_arr_decl': abs_arr_decl,
                                       })
    abs_func_decl = OGroup(dir_abs_decl_no_func, 'callee') +\
                    OneOrMore(Suppress(Literal('(')) + param_types +
                              Suppress(Literal(')')))
    dir_abs_decl <<= Alternate2R(Suppress(Literal('(')) + abstract_decl +
                                 Suppress(Literal(')')),
                                 {'abs_arr_decl': abs_arr_decl,
                                  'abs_func_decl': abs_func_decl,
                                  })
    abstract_decl <<= pointer("pointer") |\
                      (OGroup(pointer, "pointer") + dir_abs_decl("dir_abs_decl"))
    param_decl = ty_pe("type") + OGroup(regparm, "regparm") +\
                 Optional(Alternate({'decl_spec': decl_spec,
                                     'abstract_decl': abstract_decl,
                                     }))
    param_types <<= delimitedList(Group(param_decl))
    direct_decl = Forward()
    direct_decl_no_func = Alternate2(Suppress(Literal('(')) + decl_spec +
                                     Suppress(Literal(')')),
                                     [('array_decl', array_decl),
                                      ('identifier', identifier),
                                      ])
    rfunc_decl = Group(regparm)("regparm") +\
                 Group(direct_decl)("callee") +\
                 Suppress(Literal('(')) + param_types("params") +\
                 Suppress(Literal(')'))
    func_decl = OGroup(regparm, "regparm") +\
                Group(direct_decl_no_func)("callee") +\
                OneOrMore(Suppress(Literal('(')) + param_types("params") +
                          Suppress(Literal(')')))
    direct_decl <<= Alternate2R(Suppress(Literal('(')) + decl_spec +
                                Suppress(Literal(')')),
                                [('array_decl', array_decl),
                                 ('func_decl', func_decl | rfunc_decl),
                                 ('identifier', identifier),
                                 ])
    decl_spec <<= Group(OGroup(pointer, "pointer") + Group(direct_decl)("direct_decl"))
    expression = Forward()
    initialiser = Suppress(Literal('=')) + expression
    object_decl = Group(OGroup(register, 'register') + decl_spec("decl_spec") +\
                        OGroup(initialiser, 'initialiser'))
    object_decls = delimitedList(object_decl) | Empty()
    declaration = object_decls + Suppress(Literal(';')) # TODO or function-defn
    declare = Group(OGroup(storage_class, 'storage_class') +\
                    OGroup(qualifier_list, 'qualifier_list') +\
                    ty_pe("type") + declaration("declaration"))
    type_name = NoMatch() # TODO
    dec_const = Word('123456789', nums)
    hex_const = (Word('0', 'xX', exact=2) + Word(hexnums))
    oct_const = Word('0', '01234567')
    long_suffix = Word('lL', exact=1)
    int_const = (dec_const | hex_const | oct_const) + Optional(long_suffix)
    enum_const = (Literal('$') + identifier)
    c_char = Word(printables + ' ', exact=1, excludeChars="'\\")
    octal_escape = Literal('\\') + Word('01234567', max=3)
    hex_escape = Literal('\\x') + Word(hexnums, max=2)
    esc_seq = Literal(r'\n') | Literal(r'\t') | octal_escape | hex_escape
    char_const = (Literal("'") + (c_char | esc_seq) + Literal("'"))
    constant = Alternate({'int_const': int_const,
                          'enum_const': enum_const,
                          'char_const': char_const,
                          })
    string_literal = QuotedString('"', escChar='\\')
    primary_expr = Alternate({'identifier': identifier,
                              'constant': constant,
                              'string_literal': string_literal,
                              'flag_ident': flag_ident,
                              'paren_expr': Suppress(Literal('(')) +
                                            expression +
                                            Suppress(Literal(')')),
                              })
    postfix_expr = Forward()
    subscript_expr = postfix_expr("postfix_expr") + Suppress(Literal('[')) +\
                     expression("subscript") + Suppress(Literal(']'))
    funcall_expr = NoMatch() # TODO
    member_op = Literal('->') | Literal('.')
    member_expr = postfix_expr("postfix_expr") + member_op("op") + identifier("tag")
    postcrem_expr = postfix_expr("postfix_expr") + (Literal('++') | Literal('--'))("op")
    compound_lit = NoMatch() # TODO
    postfix_expr <<= Alternate2(primary_expr,
                                [('subscript_expr', subscript_expr),
                                 ('funcall_expr', funcall_expr),
                                 ('member_expr', member_expr),
                                 ('postcrem_expr', postcrem_expr),
                                 ('compount_lit', compound_lit),
                                 ])
    unary_expr = Forward()
    unary_op = Literal('&') | Literal('*') | Literal('~') | Literal('!')
    precrem_expr = (Literal('++') | Literal('--'))("op") + unary_expr("arg")
    cast_expr = Forward()
    do_cast = Suppress(Literal('(')) + type_name("type") +\
              Suppress(Literal(')')) + cast_expr("arg")
    cast_expr <<= Alternate3(unary_expr, do_cast, "do_cast")
    sizeof_arg = type_name("name") | unary_expr("unary_expr")
    sizeof_expr = Suppress(Keyword('sizeof')) + Suppress(Literal('(')) +\
                  sizeof_arg("arg") + Suppress(Literal(')'))
    unary_expr <<= Alternate2(postfix_expr,
                              {'precrem_expr': precrem_expr,
                               'unary_cast': unary_op + cast_expr,
                               'sizeof_expr': sizeof_expr,
                               })
    shift_expr = Forward()
    shift_op = Literal('<<') | Literal('>>')
    do_shift = shift_expr("left") + shift_op("op") + cast_expr("right")
    shift_expr <<= Alternate3(cast_expr, do_shift, "do_shift")
    bitwise_expr = Forward()
    bitwise_op = Literal('&') | Literal('^') | Literal('|')
    do_bitwise = bitwise_expr("left") + bitwise_op("op") + shift_expr("right")
    bitwise_expr <<= Alternate3(shift_expr, do_bitwise, "do_bitwise")
    additive_expr = Forward()
    additive_op = Literal('+') | Literal('-')
    do_additive = additive_expr("left") + additive_op("op") + bitwise_expr("right")
    additive_expr <<= Alternate3(bitwise_expr, do_additive, "do_additive")
    relation_op = Literal('<') | Literal('>') | Literal('<=') | Literal('>=')
    do_relation = additive_expr("left") + relation_op("op") + additive_expr("right")
    relation_expr = Group(do_relation)("do_relation") | additive_expr
    equality_expr = Forward()
    equality_op = Literal('==') | Literal('!=')
    do_equality = equality_expr("left") + equality_op("op") + relation_expr("right")
    equality_expr <<= Alternate3(relation_expr, do_equality, "do_equality")
    and_expr = Forward()
    do_and = and_expr("left") + Suppress(Literal('&&')) + equality_expr("right")
    and_expr <<= Alternate3(equality_expr, do_and, "do_and")
    or_expr = Forward()
    do_or = or_expr("left") + Suppress(Literal('||')) + and_expr("right")
    or_expr <<= Alternate3(and_expr, do_or, "do_or")
    ternary_expr = Forward()
    do_ternary = or_expr("cond") + Suppress(Literal('?')) + \
                 expression("true") + Suppress(Literal(':')) + \
                 ternary_expr("false")
    ternary_expr <<= Group(do_ternary)("do_ternary") | or_expr
    assign_expr = Forward()
    assign_op = Literal('=') | Literal('+=') | Literal('-=') | Literal('&=') |\
                Literal('|=') | Literal('^=') | Literal('<<=') | Literal('>>=')
    do_assign = unary_expr("left") + assign_op("op") + assign_expr("right")
    assign_expr <<= Alternate3(ternary_expr, do_assign, "do_assign")
    expression <<= delimitedList(assign_expr)
    source = OneOrMore(declare)
    source.ignore(cppStyleComment)
    @classmethod
    def parse(cls, text):
        return cls.source.parseString(text)#, parseAll=True)

## Entry point

def parse(source):
    parser = Parser()
    return parser.parse(source)

## Test code

if __name__ == "__main__":
    if len(sys.argv) > 1:
        with open(sys.argv[1], 'r') as f:
            source = f.read()
    else:
        source = sys.stdin.read()
    parser = Parser()
    result = parser.parse(source)
    print result.dump()

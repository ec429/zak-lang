#!/usr/bin/python

import re, sys, pprint
from pyparsing import *
ParserElement.enablePackrat()

## Parser

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
    return Group(q).setResultsName(n).setName(n) | p
def Litor(*args):
    return MatchFirst(Literal(s) for s in args)
def Keyor(*args):
    return Alternate([(k, Suppress(Keyword(k))) for k in args])

class Parser(object):
    identifier = Word(alphas + '_', alphanums + '_').setName("identifier")
    qualifier = Keyor('const', 'volatile')
    storage_class = Keyor('auto', 'static', 'extern')
    qualifier_list = OneOrMore(qualifier)
    ty_pe = Forward().setName("type")
    object_decls = Forward()
    struct_decl = OGroup(qualifier_list, "qualifier_list") +\
                  Group(ty_pe)("type") + Group(object_decls)("declaration") +\
                  Suppress(Literal(';'))
    struct_body = Suppress(Literal('{')) +\
                  OneOrMore(Group(struct_decl)) +\
                  Suppress(Literal('}'))
    struct = Suppress(Keyword('struct')) + identifier("stag") +\
             OGroup(struct_body, "body")
    enum_const = (Suppress(Literal('$')) + identifier("name"))
    assign_expr = Forward().setName("assign_expr")
    enum_defn = enum_const +\
                Optional(Suppress(Literal('=')) + Group(assign_expr)("value"))
    enum_body = Suppress(Literal('{')) + delimitedList(Group(enum_defn)) +\
                Suppress(Optional(Literal(','))) + Suppress(Literal('}'))
    enum = Suppress(Keyword('enum')) + identifier("etag") +\
           OGroup(enum_body, "body")
    ty_pe <<= Alternate({'void': Suppress(Keyword('void')),
                         'bool': Suppress(Keyword('bool')),
                         'byte': Suppress(Keyword('byte')),
                         'word': Suppress(Keyword('word')),
                         'struct': struct,
                         'enum': enum,
                         })
    pointer = Forward()
    pointer <<= Suppress(Literal('*')) +\
                OGroup(qualifier_list, "qualifier_list") +\
                OGroup(pointer, "pointer")
    flag_name = Literal('S') | Literal('Z') | Literal('H') |\
                Literal('P') | Literal('N') | Literal('C')
    flag_ident = (Suppress(Literal('#')) + flag_name)
    reg8 = Litor('A', 'B', 'C', 'D', 'E', 'H', 'L', 'IXH', 'IXL', 'IYH', 'IYL')
    reg16 = Litor('BC', 'DE', 'HL', 'IX', 'IY')
    regf = Optional(Literal('!'))("not") + flag_ident
    register = Alternate({'reg8': reg8, 'reg16': reg16, 'regf': regf})
    regparm = Suppress(Literal('@')) + register
    decl_spec = Forward().setName("decl_spec")
    abstract_decl = Forward().setName("abstract_decl")
    param_types = Forward().setName("param_types")
    function_decl_tail = OGroup(regparm, "regparm") +\
                         Suppress(Literal('(')) + Group(param_types)("params") +\
                         Suppress(Literal(')'))
    expression = Forward().setName("expression")
    array_decl_tail = Suppress(Literal('[')) + Group(expression)("dimension") +\
                      Suppress(Literal(']'))
    dir_abs_decl_primary = (Suppress(Literal('(')) + abstract_decl +
                            Suppress(Literal(')')))
    dir_abs_decl_tail = Alternate({'function': function_decl_tail,
                                    'array': array_decl_tail,
                                    })
    dir_abs_decl = (OGroup(dir_abs_decl_primary, "direct_decl") +
                    Group(OneOrMore(Group(dir_abs_decl_tail)))("tail")) |\
                   Group(dir_abs_decl_primary)("direct_decl")
    abstract_decl <<= (OGroup(pointer, "pointer") +
                       dir_abs_decl) |\
                      Group(pointer)("pointer")
    param_decl = Group(ty_pe)("type") + OGroup(regparm, "regparm") +\
                 Optional(Alternate([('decl_spec', decl_spec),
                                     ('abstract_decl', abstract_decl),
                                     ]))
    param_types <<= Optional(delimitedList(Group(param_decl)))
    direct_decl_primary = (Suppress(Literal('(')) + decl_spec +
                           Suppress(Literal(')'))) |\
                          identifier("identifier")
    direct_decl_tail = Alternate({'function': function_decl_tail,
                                  'array': array_decl_tail,
                                  })
    direct_decl = Forward().setName("direct_decl")
    direct_decl <<= direct_decl_primary +\
                    OGroup(OneOrMore(Group(direct_decl_tail)), "tail")
    decl_spec <<= OGroup(pointer, "pointer") + Group(direct_decl)("direct_decl")
    initialiser = Forward()
    array_designator = Suppress(Literal('[')) + Group(expression)("subscript") +\
                       Suppress(Literal(']'))
    member_designator = Suppress(Literal('.')) + identifier("tag")
    designator = Alternate({'array': array_designator,
                            'member': member_designator,
                            })
    designation = OneOrMore(Group(designator)) + Suppress(Literal('='))
    designated_initialiser = OGroup(designation, "designation") +\
                             Group(initialiser)("initialiser")
    initialiser_list = delimitedList(Group(designated_initialiser)) +\
                       Optional(Suppress(Literal(',')))
    init_list = Suppress(Literal('{')) + Group(initialiser_list)("init_list") +\
                Suppress(Literal('}'))
    initialiser <<= (assign_expr | init_list)
    object_decl = Group(decl_spec)("decl_spec") +\
                  OGroup(Suppress(Literal('=')) + initialiser, 'initialiser')
    object_decls <<= delimitedList(Group(object_decl)) | Empty()
    declaration = object_decls + Suppress(Literal(';'))
    declare = Group(OGroup(storage_class, 'storage_class') +
                    OGroup(qualifier_list, 'qualifier_list') +
                    Group(ty_pe)("type") + Group(declaration)("declaration"))
    declare_list = OneOrMore(declare)
    block_stmt = Forward()
    expr_stmt = expression + Suppress(Literal(';'))
    statement = Forward()
    else_clause = Suppress(Keyword('else')) + statement
    if_stmt = Suppress(Keyword('if')) + Suppress(Literal('(')) +\
              Group(expression)("condition") + Suppress(Literal(')')) +\
              Group(statement)("true") + OGroup(else_clause, "false")
    goto_stmt = Suppress(Keyword('goto')) + identifier("label") +\
                Suppress(Literal(';'))
    label_stmt = identifier("label") + Suppress(Literal(':'))
    return_stmt = Suppress(Keyword('return')) + OGroup(expression, "value") +\
                  Suppress(Literal(';'))
    statement <<= Alternate({'expr_stmt': expr_stmt,
                             'if_stmt': if_stmt,
                             'goto_stmt': goto_stmt,
                             'label_stmt': label_stmt,
                             'return_stmt': return_stmt,
                             'block_stmt': block_stmt,
                             })
    stmt_list = OneOrMore(Group(statement))
    block_stmt <<= Suppress(Literal('{')) +\
                   OGroup(declare_list, "declare_list") +\
                   OGroup(stmt_list, "stmt_list") +\
                   Suppress(Literal('}'))
    function_defn = Group(OGroup(storage_class, 'storage_class') +
                          OGroup(qualifier_list, 'qualifier_list') +
                          Group(ty_pe)("type") + Group(decl_spec)("decl_spec") +
                          block_stmt)("function_defn")
    type_name = ty_pe("type") + abstract_decl("abstract_decl")
    dec_const = Word('123456789', nums)
    hex_const = Suppress(Word('0', 'xX', exact=2)) + Word(hexnums)
    oct_const = Word('0', '01234567')
    long_suffix = Suppress(Word('lL', exact=1))
    int_const = Alternate({'dec': dec_const,
                           'hex': hex_const,
                           'oct': oct_const,
                           }) + OGroup(long_suffix, "long")
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
    subscript_tail = Suppress(Literal('[')) + Group(expression)("subscript") +\
                     Suppress(Literal(']'))
    arg_expr_list = delimitedList(Group(assign_expr))
    funcall_tail = Suppress(Literal('(')) +\
                   Group(arg_expr_list + Optional(Suppress(Literal(','))))\
                          ("arg_list") + Suppress(Literal(')'))
    member_op = Literal('->') | Literal('.')
    member_tail = member_op("op") + identifier("tag")
    postcrem_tail = (Literal('++') | Literal('--'))("op")
    postfix_tail = Alternate({'subscript_tail': subscript_tail,
                              'funcall_tail': funcall_tail,
                              'member_tail': member_tail,
                              'postcrem_tail': postcrem_tail,
                              })
    postfix_expr = (Group(primary_expr)("primary_expr") + OneOrMore(Group(postfix_tail))("postfix_tail")) |\
                   primary_expr
    unary_expr = Forward().setName("unary_expr")
    unary_op = Literal('&') | Literal('*') | Literal('~') | Literal('!')
    precrem_expr = (Literal('++') | Literal('--'))("op") + Group(unary_expr)("arg")
    cast_expr = Forward().setName("cast_expr")
    do_cast = Suppress(Literal('(')) + Group(type_name)("type") +\
              Suppress(Literal(')')) + Group(cast_expr)("arg")
    cast_expr <<= Alternate3(unary_expr, do_cast, "do_cast")
    sizeof_arg = type_name("type") | unary_expr("expr")
    sizeof_expr = Suppress(Keyword('sizeof')) + Suppress(Literal('(')) +\
                  Group(sizeof_arg)("arg") + Suppress(Literal(')'))
    unary_expr <<= Alternate2(postfix_expr,
                              {'precrem_expr': precrem_expr,
                               'unary_expr': unary_op("op") +
                                             Group(cast_expr)("arg"),
                               'sizeof_expr': sizeof_expr,
                               })
    shift_expr = Forward().setName("shift_expr")
    shift_op = Literal('<<') | Literal('>>')
    do_shift = Group(cast_expr)("left") + shift_op("op") +\
               Group(shift_expr)("right")
    shift_expr <<= Alternate3(cast_expr, do_shift, "do_shift")
    bitwise_expr = Forward().setName("bitwise_expr")
    bitwise_op = Literal('&') | Literal('^') | Literal('|')
    do_bitwise = Group(shift_expr)("left") + bitwise_op("op") +\
                 Group(bitwise_expr)("right")
    bitwise_expr <<= Alternate3(shift_expr, do_bitwise, "do_bitwise")
    additive_expr = Forward().setName("additive_expr")
    additive_op = Literal('+') | Literal('-')
    do_additive = Group(bitwise_expr)("left") + additive_op("op") +\
                  Group(additive_expr)("right")
    additive_expr <<= Alternate3(bitwise_expr, do_additive, "do_additive")
    relation_op = Literal('<') | Literal('>') | Literal('<=') | Literal('>=')
    do_relation = Group(additive_expr)("left") + relation_op("op") +\
                  Group(additive_expr)("right")
    relation_expr = Alternate3(additive_expr, do_relation, "do_relation")
    equality_expr = Forward().setName("equality_expr")
    equality_op = Literal('==') | Literal('!=')
    do_equality = Group(relation_expr)("left") + equality_op("op") +\
                  Group(equality_expr)("right")
    equality_expr <<= Alternate3(relation_expr, do_equality, "do_equality")
    and_expr = Forward().setName("and_expr")
    do_and = Group(equality_expr)("left") + Suppress(Literal('&&')) +\
             Group(and_expr)("right")
    and_expr <<= Alternate3(equality_expr, do_and, "do_and")
    or_expr = Forward().setName("or_expr")
    do_or = Group(and_expr)("left") + Suppress(Literal('||')) +\
            Group(or_expr)("right")
    or_expr <<= Alternate3(and_expr, do_or, "do_or")
    ternary_expr = Forward().setName("ternary_expr")
    do_ternary = Group(or_expr)("cond") + Suppress(Literal('?')) + \
                 Group(expression)("true") + Suppress(Literal(':')) + \
                 Group(ternary_expr)("false")
    ternary_expr <<= Alternate3(or_expr, do_ternary, "do_ternary")
    assign_op = Literal('=') | Literal('+=') | Literal('-=') | Literal('&=') |\
                Literal('|=') | Literal('^=') | Literal('<<=') | Literal('>>=')
    do_assign = Group(unary_expr)("left") + assign_op("op") +\
                Group(assign_expr)("right")
    assign_expr <<= Alternate3(ternary_expr, do_assign, "do_assign")
    do_comma = Group(assign_expr)("left") + Suppress(Literal(',')) +\
               Group(expression)("right")
    expression <<= Alternate3(assign_expr, do_comma, "do_comma")
    source = OneOrMore(Group(declare("declare") | function_defn))
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

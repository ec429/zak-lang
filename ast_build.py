#!/usr/bin/python

import sys, pprint
import parser
PAR = parser.Parser

class ASTError(Exception): pass
class UnhandledEntity(ASTError):
    def __init__(self, entity):
        self.entity = entity
    def __str__(self):
        return "%s\ncould not handle entity" % (self.entity.dump(),)

class Type(object):
    name = None
    def __str__(self):
        return self.name

class Void(Type):
    name = 'void'
class Bool(Type):
    name = 'bool'
class Byte(Type):
    name = 'byte'
class Word(Type):
    name = 'word'

def get_type(typ):
    if typ.get('void') is not None:
        return Void()
    if typ.get('bool') is not None:
        return Bool()
    if typ.get('byte') is not None:
        return Byte()
    if typ.get('word') is not None:
        return Word()

class StorageClass(object):
    def __init__(self, sc):
        self.sc = sc
    def __str__(self):
        return self.sc

class DeclIdentifier(object):
    def __init__(self, ident, typ):
        self.ident = ident
        self.typ = typ
    def __str__(self):
        return str(self.typ)

def Param(param):
    typ = get_type(param['type'])
    if typ is None:
        raise UnhandledEntity(param)
    if param.get('decl_spec') is not None:
        return DirectDecl(param['decl_spec'], typ)
    if param.get('abstract_decl') is not None:
        return DirectDecl(param['abstract_decl'], typ)
    return DeclIdentifier(None, typ)

class Function(object):
    def __init__(self, ftail, ret):
        self.ret = ret
        self.params = [Param(p) for p in ftail['params']]
    def __str__(self):
        def pstr(p):
            if p.ident is not None:
                return '%s as %s'%(p.ident, p)
            return str(p)
        return 'function [%s -> %s]' % (', '.join(map(pstr, self.params)),
                                        self.ret)

def DirectDecl(direct_decl, typ):
    # <direct-decl>   ::= <identifier> | '(' <decl-spec> ')' | <array-decl> | <func-decl>
    tail = direct_decl.get('tail')
    if tail is not None:
        for tail_part in reversed(tail):
            if tail_part.get('function') is not None:
                typ = Function(tail_part['function'], typ)
            if tail_part.get('array') is not None:
                raise UnhandledEntity(tail_part['array'])
    pointer = direct_decl.get('pointer')
    if pointer is not None:
        typ = Pointer(pointer, typ)
    if direct_decl.get('direct_decl') is not None:
        if direct_decl.get('identifier') is not None:
            raise UnhandledEntity(direct_decl)
        return DirectDecl(direct_decl['direct_decl'], typ)
    return DeclIdentifier(direct_decl.get('identifier'), typ)

class Pointer(object):
    # <pointer>       ::= '*' <qualifier-list>? <pointer>?
    def __init__(self, pointer, target):
        if pointer.get('qualifier_list') is not None:
            raise UnhandledEntity(pointer['qualifier_list'])
        if pointer.get('pointer') is not None:
            target = Pointer(pointer['pointer'], target)
        self.target = target
    def __str__(self):
        return 'Pointer(%s)'%(self.target,)

class DeclSpec(object):
    def __init__(self, decl_spec, typ):
        # <decl-spec>    ::= <pointer>? <direct-decl>
        pointer = decl_spec.get('pointer')
        if pointer is not None:
            typ = Pointer(pointer, typ)
        if decl_spec.get('direct_decl') is None:
            direct_decl = DeclIdentifier(None, typ)
        else:
            direct_decl = DirectDecl(decl_spec['direct_decl'], typ)
        tail = decl_spec.get('tail')
        if tail is not None:
            raise UnhandledEntity(tail)
        self.object = direct_decl
        self.ident = self.object.ident
    def __str__(self):
        return '%s as %s'%(self.ident, self.object)

def IntConst(expr):
    if expr.get('dec') is not None:
        return int(expr['dec'][0], 10)
    if expr.get('hex') is not None:
        return int(expr['hex'][0], 16)
    if expr.get('oct') is not None:
        return int(expr['oct'][0], 8)
    raise UnhandledEntity(expr)

def Constant(expr):
    if expr.get('int_const') is not None:
        return IntConst(expr['int_const'])
    if expr.get('enum_const') is not None:
        raise UnhandledEntity(expr['enum_const'])
    if expr.get('char_const') is not None:
        raise UnhandledEntity(expr['char_const'])
    raise UnhandledEntity(expr)

class Identifier(object):
    def __init__(self, ident):
        self.ident = ident[0]
    def __str__(self):
        return self.ident

def DoPrimary(expr):
    if expr.get('identifier') is not None:
        return Identifier(expr['identifier'])
    if expr.get('constant') is not None:
        return Constant(expr['constant'])
    if expr.get('string_literal') is not None:
        raise UnhandledEntity(expr['string_literal'])
    if expr.get('flag_ident') is not None:
        raise UnhandledEntity(expr['flag_ident'])
    if expr.get('paren_expr') is not None:
        raise UnhandledEntity(expr['paren_expr'])
    raise UnhandledEntity(expr)

def DoPostfix(expr):
    if expr.get('postfix_tail') is not None:
        raise UnhandledEntity(expr['postfix_tail'])
    return DoPrimary(expr)

def DoUnary(expr):
    if expr.get('precrem_expr') is not None:
        raise UnhandledEntity(expr['precrem_expr'])
    if expr.get('unary_expr') is not None:
        raise UnhandledEntity(expr['unary_expr'])
    if expr.get('sizeof_expr') is not None:
        raise UnhandledEntity(expr['sizeof_expr'])
    return DoPostfix(expr);

def DoCast(expr):
    if expr.get('do_cast') is not None:
        raise UnhandledEntity(expr['do_cast'])
    return DoUnary(expr)

class BinaryExpr(object):
    def __str__(self):
        return '%s(%s %s %s)'%(self.__class__.__name__,
                               self.left, self.op, self.right)

def DoShift(expr):
    if expr.get('do_shift') is not None:
        raise UnhandledEntity(expr['do_shift'])
    return DoCast(expr)

def DoBitwise(expr):
    if expr.get('do_bitwise') is not None:
        raise UnhandledEntity(expr['do_bitwise'])
    return DoShift(expr)

def DoAdditive(expr):
    if expr.get('do_additive') is not None:
        raise UnhandledEntity(expr['do_additive'])
    return DoBitwise(expr)

def DoRelation(expr):
    if expr.get('do_relation') is not None:
        raise UnhandledEntity(expr['do_relation'])
    return DoAdditive(expr)

class EqualityExpr(BinaryExpr):
    def __init__(self, expr):
        self.left = DoRelation(expr['left'])
        self.op = expr['op']
        self.right = DoEquality(expr['right'])

def DoEquality(expr):
    # <equality-expr> ::= <relation-expr> | <relation-expr> ('==' | '!=') <equality-expr>
    if expr.get('do_equality') is not None:
        return EqualityExpr(expr['do_equality'])
    return DoRelation(expr)

def DoAnd(expr):
    if expr.get('do_and') is not None:
        raise UnhandledEntity(expr['do_and'])
    return DoEquality(expr)

def DoOr(expr):
    if expr.get('do_or') is not None:
        raise UnhandledEntity(expr['do_or'])
    return DoAnd(expr)

def DoTernary(expr):
    # <ternary-expr>  ::= <or-expr> | <or-expr> '?' <expression> ':' <ternary-expr>
    if expr.get('do_ternary') is not None:
        raise UnhandledEntity(expr['do_ternary'])
    return DoOr(expr)

def DoAssign(expr):
    # <assign-expr>   ::= <ternary-expr> | <unary-expr> <assign-op> <assign-expr>
    if expr.get('do_assign') is not None:
        raise UnhandledEntity(expr['do_assign'])
    return DoTernary(expr)

def DoExpression(expr):
    # <expression>    ::= <assign-expr> | <assign-expr> ',' <expression>
    if expr.get('do_comma') is not None:
        raise UnhandledEntity(expr['do_comma'])
    return DoAssign(expr)

def Initialiser(init):
    # '=' (<expression> | '{' <init-list> ','? '}')
    if init.get('init_list') is not None:
        raise UnhandledEntity(init['init_list'])
    return DoAssign(init)

class Declaration(object):
    # <object-decl>   ::= <decl-spec> <initialiser>
    def __init__(self, declaration, sc, typ):
        self.sc = sc
        self.decl_spec = DeclSpec(declaration['decl_spec'], typ)
        self.init = declaration.get('initialiser')
        if self.init is not None:
            self.init = Initialiser(self.init)
    def __str__(self):
        s = str(self.decl_spec)
        if self.sc is not None:
            s = '%s %s' % (self.sc, s)
        if self.init is not None:
            s = '%s initially %s' % (s, self.init)
        return s

class Declare(object):
    # <declare>       ::= <storage-class>? <qualifier-list>? <type> <declaration>
    def __init__(self, declare):
        self.sc = declare.get('storage_class')
        if self.sc is not None:
            if self.sc.get('static') is not None:
                self.sc = StorageClass('static')
            elif self.sc.get('extern') is not None:
                self.sc = StorageClass('extern')
            elif self.sc.get('auto') is not None:
                self.sc = StorageClass('auto')
            else:
                raise UnhandledEntity(self.sc)
        if declare.get('qualifier_list') is not None:
            raise UnhandledEntity(declare['qualifier_list'])
        self.typ = get_type(declare['type'])
        if self.typ is None:
            raise UnhandledEntity(declare['type'])
        # <declaration>   ::= <object-decls> ';' | <function-defn>
        # <object-decls>  ::= <object-decl> (',' <object-decls>)?
        self.declarations = [Declaration(d, self.sc, self.typ) for d in declare['declaration']]
    def __str__(self):
        return '\n'.join(['declare %s'%(d,) for d in  self.declarations])

class ReturnStatement(object):
    def __init__(self, rs):
        self.value = rs.get('value')
        if self.value is not None:
            self.value = DoExpression(self.value)
    def __str__(self):
        if self.value is None:
            return 'return;'
        return 'return %s;' % (self.value,)

def Statement(stmt):
    if stmt.get('return_stmt') is not None:
        return ReturnStatement(stmt['return_stmt'])
    raise UnhandledEntity(stmt)

class BlockStatement(object):
    def __init__(self, block):
        if block.get('declare_list') is not None:
            raise UnhandledEntity(block['declare_list'])
        stmts = block.get('stmt_list', [])
        self.stmts = [Statement(stmt) for stmt in stmts]
    def __str__(self):
        return ' '.join(map(str, ['{'] + self.stmts + ['}']))

class FunctionDefn(object):
    # <function-defn> ::= <storage-class>? <qualifier-list>? <type> <decl_spec> <block-stmt>
    def __init__(self, defn):
        self.sc = defn.get('storage_class')
        if self.sc is not None:
            if self.sc.get('static') is not None:
                self.sc = StorageClass('static')
            elif self.sc.get('extern') is not None:
                self.sc = StorageClass('extern')
            elif self.sc.get('auto') is not None:
                self.sc = StorageClass('auto')
            else:
                raise UnhandledEntity(self.sc)
        if defn.get('qualifier_list') is not None:
            raise UnhandledEntity(defn['qualifier_list'])
        self.typ = get_type(defn['type'])
        if self.typ is None:
            raise UnhandledEntity(defn['type'])
        self.decl_spec = DeclSpec(defn['decl_spec'], self.typ)
        self.body = BlockStatement(defn)
    def __str__(self):
        s = str(self.decl_spec)
        if self.sc is not None:
            s = '%s %s' % (self.sc, s)
        return 'define %s body %s' % (s, self.body)

class AST_builder(object):
    def __init__(self, parse_tree):
        self.decls = []
        try:
            for entity in parse_tree:
                if entity.get('declare'):
                    self.decls.append(Declare(entity['declare']))
                elif entity.get('function_defn'):
                    self.decls.append(FunctionDefn(entity['function_defn']))
                else:
                    raise UnhandledEntity(entity)
        finally:
            for decl in self.decls:
                print decl

## Test code

if __name__ == "__main__":
    if len(sys.argv) > 1:
        with open(sys.argv[1], 'r') as f:
            source = f.read()
    else:
        source = sys.stdin.read()
    parse_tree = parser.parse(source)
    print "Parse tree:"
    pprint.pprint(parse_tree)
    print
    ast = AST_builder(parse_tree)

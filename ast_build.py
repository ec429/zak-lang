#!/usr/bin/python

import sys, pprint
import parser
PAR = parser.Parser

class ASTError(Exception): pass
class UnhandledEntity(ASTError):
    def __init__(self, entity):
        self.entity = entity
    def __str__(self):
        if isinstance(self.entity, parser.ParseResults):
            dump = self.entity.dump()
        else:
            dump = pprint.pformat(self.entity)
        return '\n'.join((dump, "could not handle entity"))

class Type(object):
    fixed_size = None
    def compat(self, other):
        raise NotImplementedError(self, other)
    def common(self, other):
        """Returns the appropriate common type for self and other.
        Some subclasses will need to override this.

        Check self.compat(other) before calling!"""
        return self
    def __eq__(self, other):
        """Stricter than compat, this is used for pointee equality."""
        raise NotImplementedError(self, other)
    def __ne__(self, other):
        return not self == other
    @classmethod
    def build(cls, *args):
        raise NotImplementedError(cls, *args)
    def __repr__(self):
        return str(self)
    def qualifiers(self):
        return set()
    def unqualified(self):
        return self

class Qualified(Type):
    qualifier = None
    def __init__(self, typ):
        self.typ = typ
    def __str__(self):
        return '%s %s'%(self.qualifier, self.typ)
    def qualifiers(self):
        return set(self.qualifier) | self.typ.qualifiers()
    def unqualified(self):
        return self.typ
class Const(Qualified):
    qualifier = 'const'
class Volatile(Qualified):
    qualifier = 'volatile'
def get_qualifier(qual):
    for q in [Const, Volatile]:
        if qual == q.qualifier:
            return q
    raise ASTError("No such qualifier", qual)
def qualify(qualifiers, t):
    for q in qualifiers:
        t = get_qualifier(q)(t)
    return t
def build_qualifiers(ql, t):
    if ql.get('const') is not None:
        t = Const(t)
    if ql.get('volatile') is not None:
        t = Volatile(t)
    return t

class PrimitiveType(Type):
    name = None
    def __str__(self):
        return self.name
    def compat(self, other):
        if isinstance(other, Enum):
            return self.compat(other.typ)
        return self == other
    def __eq__(self, other):
        return isinstance(other, PrimitiveType) and self.name == other.name
class Void(PrimitiveType):
    name = 'void'
    fixed_size = 1
class Bool(PrimitiveType):
    name = 'bool'
    fixed_size = 1
class Byte(PrimitiveType):
    name = 'byte'
    fixed_size = 1
    @classmethod
    def make(cls, val):
        return IntConst(val, False)
class Word(PrimitiveType):
    name = 'word'
    fixed_size = 2
    def compat(self, other):
        if Byte().compat(other):
            return True
        return super(Word, self).compat(other)
    @classmethod
    def make(cls, val):
        return IntConst(val, True)

class Struct(Type):
    def __init__(self, tag, body):
        self.tag = tag
        self.body = body
    @classmethod
    def build(cls, struct):
        body = struct.get('body')
        if body is not None:
            body = [Declare(d) for d in body]
        return cls(struct['stag'],
                   body)
    def __str__(self):
        body = ''
        if self.body is not None:
            body = ' '.join(map(str, [' {'] + self.body + ['}']))
        return 'struct %s%s' % (self.tag, body)
    def __eq__(self, other):
        return isinstance(other, Struct) and self.tag == other.tag
    compat = __eq__

class EnumValue(object):
    def __init__(self, name, value):
        self.name = name
        self.value = value
    @classmethod
    def build(cls, ev):
        value = ev.get('value')
        if value is not None:
            value = DoAssign(value)
        return cls(ev['name'], value)
    def __str__(self):
        if self.value is None:
            return '$%s' % (self.name,)
        return '$%s = %s' % (self.name, self.value)

class Enum(Type):
    def __init__(self, tag, body, typ):
        self.tag = tag
        self.body = body
        self.typ = typ
    @classmethod
    def build(cls, enum):
        body = enum.get('body')
        typ = None
        if body is not None:
            typ = get_type(body['type'])
            body = [EnumValue.build(e) for e in body['values']]
        return cls(enum['etag'], body, typ)
    def __str__(self):
        body = ''
        if self.body is not None:
            body = ' %s {%s}' % (self.typ, ', '.join(map(str, self.body)))
        return 'enum %s%s' % (self.tag, body)
    def __eq__(self, other):
        return isinstance(other, Enum) and self.tag == other.tag
    compat = __eq__

def get_type(typ):
    if typ.get('void') is not None:
        return Void()
    if typ.get('bool') is not None:
        return Bool()
    if typ.get('byte') is not None:
        return Byte()
    if typ.get('word') is not None:
        return Word()
    if typ.get('struct') is not None:
        return Struct.build(typ['struct'])
    if typ.get('enum') is not None:
        return Enum.build(typ['enum'])

class StorageClass(object):
    def __init__(self, sc):
        self.sc = sc
    @property
    def auto(self):
        return self.sc == 'auto'
    @property
    def extern(self):
        return self.sc == 'extern'
    @property
    def static(self):
        return self.sc == 'static'
    def __str__(self):
        return self.sc
    __repr__ = __str__

Auto = StorageClass('auto')
Extern = StorageClass('extern')
Static = StorageClass('static')

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
    if param.get('qualifier_list') is not None:
        typ = build_qualifiers(param['qualifier_list'], typ)
    if param.get('decl_spec') is not None:
        return DirectDecl(param['decl_spec'], typ)
    if param.get('abstract_decl') is not None:
        return DirectDecl(param['abstract_decl'], typ)
    return DeclIdentifier(None, typ)

class Function(Type):
    def __init__(self, params, ret):
        self.params = params
        self.ret = ret
    @classmethod
    def build(cls, ftail, ret):
        return cls([Param(p) for p in ftail['params']],
                   ret)
    def __str__(self):
        def pstr(p):
            if p.ident is not None:
                return '%s as %s'%(p.ident, p)
            return str(p)
        return 'function [%s -> %s]' % (', '.join(map(pstr, self.params)),
                                        self.ret)
    def __eq__(self, other):
        # TODO regparms are unordered, will need to be separate from params
        # XXX also, functions don't care how their params are qualified
        return isinstance(other, Function) and self.ret == other.ret and \
               self.params == other.params

class Array(Type):
    def __init__(self, dim, etyp):
        self.dim = dim
        self.type = etyp
    @classmethod
    def build(cls, atail, etyp):
        return cls(DoExpression(atail['dimension']), etyp)
    def __str__(self):
        return 'array [%s] of %s' % (self.dim, self.type)
    def __eq__(self, other):
        if not isinstance(other, Array):
            return False
        if self.type != other.type:
            return False
        assert isinstance(self.dim, IntConst), self
        assert isinstance(other.dim, IntConst), other
        return self.dim.value == other.dim.value

def DirectDecl(direct_decl, typ):
    # <direct-decl>   ::= <identifier> | '(' <decl-spec> ')' | <array-decl> | <func-decl>
    tail = direct_decl.get('tail')
    if tail is not None:
        for tail_part in reversed(tail):
            if tail_part.get('function') is not None:
                typ = Function.build(tail_part['function'], typ)
            if tail_part.get('array') is not None:
                typ = Array.build(tail_part['array'], typ)
    pointer = direct_decl.get('pointer')
    if pointer is not None:
        typ = Pointer.build(pointer, typ)
    if direct_decl.get('direct_decl') is not None:
        if direct_decl.get('identifier') is not None:
            raise UnhandledEntity(direct_decl)
        return DirectDecl(direct_decl['direct_decl'], typ)
    return DeclIdentifier(direct_decl.get('identifier'), typ)

def DirAbsDecl(dir_abs_decl, typ):
    # dir-abs-decl    ::= '(' <abstract-decl> ')' | <abs-arr-decl> | <abs-func-decl>
    d = DirectDecl(dir_abs_decl, typ)
    assert isinstance(d, DeclIdentifier), d
    if d.ident is not None: # shouldn't be possible
        raise UnhandledEntity(d)
    return d.typ

class Pointer(Type):
    fixed_size = 2
    # <pointer>       ::= '*' <qualifier-list>? <pointer>?
    def __init__(self, target):
        self.target = target
    @classmethod
    def build(cls, pointer, target):
        if pointer.get('qualifier_list') is not None:
            raise UnhandledEntity(pointer['qualifier_list'])
        if pointer.get('pointer') is not None:
            target = Pointer.build(pointer['pointer'], target)
        return cls(target)
    def __str__(self):
        return 'Pointer(%s)'%(self.target,)
    def compat(self, other):
        if isinstance(other, Array):
            # decay it to a pointer
            other = Pointer(other.type)
        if isinstance(other, Pointer):
            # can't discard qualifiers, but can add them
            if self.target.qualifiers() < other.target.qualifiers():
                return False
            st = self.target.unqualified()
            ot = other.target.unqualified()
            # may freely convert to or from Pointer(Void())
            if isinstance(st, Void):
                return True
            if isinstance(ot, Void):
                return True
            # otherwise require targets to match
            return st == ot
        return False
    def common(self, other):
        if isinstance(other, Array):
            raise UnhandledEntity(other)
        if isinstance(other, Pointer):
            qualifiers = self.target.qualifiers() | other.target.qualifiers()
            st = self.target.unqualified()
            ot = other.target.unqualified()
            # may freely convert to or from Pointer(Void())
            if isinstance(st, Void):
                return qualify(qualifiers, ot)
            # ot is Void() or st == ot
            return qualify(qualifiers, st)
        raise ASTError(self, "has no common type with", other)
    def __eq__(self, other):
        if not isinstance(other, Pointer):
            return False
        return self.target == other.target

class DeclSpec(object):
    def __init__(self, decl_spec, typ):
        # <decl-spec>    ::= <pointer>? <direct-decl>
        pointer = decl_spec.get('pointer')
        if pointer is not None:
            typ = Pointer.build(pointer, typ)
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

class IntConst(object):
    def __init__(self, value, long):
        self.value = value
        self.long = long
        self.typ = Word() if self.long else Byte()
        self.size = self.typ.fixed_size
    @classmethod
    def build(cls, expr):
        if expr.get('dec') is not None:
            value = int(expr['dec'][0], 10)
        elif expr.get('hex') is not None:
            value = int(expr['hex'][0], 16)
        elif expr.get('oct') is not None:
            value = int(expr['oct'][0], 8)
        else:
            raise UnhandledEntity(expr)
        return cls(value, expr.get('long') is not None)
    def __str__(self):
        return str(self.value) + ('l' if self.long else '')

class EnumConst(object):
    def __init__(self, name):
        self.name = name
    @classmethod
    def build(cls, expr):
        return cls(expr['name'])
    def __str__(self):
        return '$%s' % (self.name,)

def DoConstant(expr):
    if expr.get('int_const') is not None:
        return IntConst.build(expr['int_const'])
    if expr.get('enum_const') is not None:
        return EnumConst.build(expr['enum_const'])
    if expr.get('char_const') is not None:
        raise UnhandledEntity(expr['char_const'])
    raise UnhandledEntity(expr)

class StringLiteral(object):
    def __init__(self, text):
        self.text = text
    @classmethod
    def build(cls, expr):
        return cls(expr[0])
    def __str__(self):
        return repr(self.text)

class Identifier(object):
    def __init__(self, ident):
        self.ident = ident
    @classmethod
    def build(cls, expr):
        return cls(expr[0])
    def __str__(self):
        return self.ident
    def __repr__(self):
        return '%s(%s)' % (self.__class__.__name__, self)

class FlagIdent(object):
    def __init__(self, flag):
        self.flag = flag
    @classmethod
    def build(cls, expr):
        return cls(expr[0])
    def __str__(self):
        return '# %s' % (self.flag)

def DoPrimary(expr):
    if expr.get('identifier') is not None:
        return Identifier.build(expr['identifier'])
    if expr.get('constant') is not None:
        return DoConstant(expr['constant'])
    if expr.get('string_literal') is not None:
        return StringLiteral.build(expr['string_literal'])
    if expr.get('flag_ident') is not None:
        return FlagIdent.build(expr['flag_ident'])
    if expr.get('paren_expr') is not None:
        raise UnhandledEntity(expr['paren_expr'])
    raise UnhandledEntity(expr)

class PostcremExpr(object):
    def __init__(self, op, target):
        self.op = op
        self.target = target
    @classmethod
    def build(cls, expr, target):
        return cls(expr['op'], target)
    def __str__(self):
        return 'PostcremExpr(%s %s)' % (self.target, self.op)

class MemberExpr(object):
    def __init__(self, op, tag, target):
        self.op = op
        self.tag = tag
        self.target = target
    @classmethod
    def build(cls, expr, target):
        return cls(expr['op'], expr['tag'], target)
    def __str__(self):
        return 'MemberExpr(%s %s %s)' % (self.target, self.op, self.tag)

class FuncallExpr(object):
    def __init__(self, args, target):
        self.args = args
        self.target = target
    @classmethod
    def build(cls, expr, target):
        return cls([DoAssign(a) for a in expr.get('arg_list', [])],
                   target)
    def __str__(self):
        return 'FuncallExpr(%s)' % (' '.join(map(str, [self.target] + self.args)),)

class SubscriptExpr(object):
    def __init__(self, subscript, target):
        self.subscript = subscript
        self.target = target
    @classmethod
    def build(cls, expr, target):
        return cls(DoExpression(expr['subscript']),
                   target)
    def __str__(self):
        return 'SubscriptExpr(%s %s)' % (self.target, self.subscript)

def DoPostfixPart(expr, target):
    if expr.get('subscript_tail') is not None:
        return SubscriptExpr.build(expr['subscript_tail'], target)
    if expr.get('funcall_tail') is not None:
        return FuncallExpr.build(expr['funcall_tail'], target)
    if expr.get('postcrem_tail') is not None:
        return PostcremExpr.build(expr['postcrem_tail'], target)
    if expr.get('member_tail') is not None:
        return MemberExpr.build(expr['member_tail'], target)
    raise UnhandledEntity(expr)

def DoPostfix(expr):
    if expr.get('postfix_tail') is not None:
        target = DoPrimary(expr['primary_expr'])
        for tail_part in expr['postfix_tail']:
            target = DoPostfixPart(tail_part, target)
        return target
    return DoPrimary(expr)

class UnaryExpr(object):
    # <unary-op> <cast-expr>
    def __init__(self, op, arg):
        self.op = op
        self.arg = arg
    @classmethod
    def build(cls, expr):
        return cls(expr['op'],
                   DoCast(expr['arg']))
    def __str__(self):
        return 'UnaryExpr(%s %s)'%(self.op, self.arg)

class PrecremExpr(object):
    def __init__(self, op, arg):
        self.op = op
        self.arg = arg
    @classmethod
    def build(cls, expr):
        return cls(expr['op'],
                   DoUnary(expr['arg']))
    def __str__(self):
        return 'PrecremExpr(%s %s)' % (self.op, self.arg)

def DoUnary(expr):
    if expr.get('precrem_expr') is not None:
        return PrecremExpr.build(expr['precrem_expr'])
    if expr.get('unary_expr') is not None:
        return UnaryExpr.build(expr['unary_expr'])
    if expr.get('sizeof_expr') is not None:
        raise UnhandledEntity(expr['sizeof_expr'])
    return DoPostfix(expr);

class CastExpr(object):
    # '(' <type-name> (',' <type-name>)? ')' <cast-expr>
    # XXX parser doesn't support two-type casts yet
    def __init__(self, typ, arg):
        self.typ = typ
        self.arg = arg
    @classmethod
    def build(cls, expr):
        type_name = expr['type']
        typ = get_type(type_name['type'])
        if typ is None:
            raise UnhandledEntity(type_name)
        if type_name.get('qualifier_list') is not None:
            typ = build_qualifiers(type_name['qualifier_list'], typ)
        if type_name.get('abstract_decl') is not None:
            typ = DirAbsDecl(type_name['abstract_decl'], typ)
        return cls(typ, DoCast(expr['arg']))
    def __str__(self):
        return '%s(%s %s)'%(self.__class__.__name__, self.typ, self.arg)

def DoCast(expr):
    if expr.get('do_cast') is not None:
        return CastExpr.build(expr['do_cast'])
    return DoUnary(expr)

class BinaryExpr(object):
    def __init__(self, left, op, right):
        self.left = left
        self.op = op
        self.right = right
    @classmethod
    def build(cls, expr):
        raise NotImplementedError()
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

class AdditiveExpr(BinaryExpr):
    @classmethod
    def build(cls, expr):
        return cls(DoBitwise(expr['left']),
                   expr['op'],
                   DoAdditive(expr['right']))

def DoAdditive(expr):
    if expr.get('do_additive') is not None:
        return AdditiveExpr.build(expr['do_additive'])
    return DoBitwise(expr)

class RelationExpr(BinaryExpr):
    @classmethod
    def build(cls, expr):
        return cls(DoAdditive(expr['left']),
                   expr['op'],
                   DoAdditive(expr['right']))

def DoRelation(expr):
    if expr.get('do_relation') is not None:
        return RelationExpr.build(expr['do_relation'])
    return DoAdditive(expr)

class EqualityExpr(BinaryExpr):
    @classmethod
    def build(cls, expr):
        return cls(DoRelation(expr['left']),
                   expr['op'],
                   DoEquality(expr['right']))

def DoEquality(expr):
    # <equality-expr> ::= <relation-expr> | <relation-expr> ('==' | '!=') <equality-expr>
    if expr.get('do_equality') is not None:
        return EqualityExpr.build(expr['do_equality'])
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

class AssignExpr(BinaryExpr):
    @classmethod
    def build(cls, expr):
        return cls(DoUnary(expr['left']),
                   expr['op'],
                   DoAssign(expr['right']))

def DoAssign(expr):
    # <assign-expr>   ::= <ternary-expr> | <unary-expr> <assign-op> <assign-expr>
    if expr.get('do_assign') is not None:
        return AssignExpr.build(expr['do_assign'])
    return DoTernary(expr)

def DoExpression(expr):
    # <expression>    ::= <assign-expr> | <assign-expr> ',' <expression>
    if expr.get('do_comma') is not None:
        raise UnhandledEntity(expr['do_comma'])
    return DoAssign(expr)

class MemberDesignator(object):
    def __init__(self, d):
        self.tag = d['tag']
    def __str__(self):
        return '.%s' % (self.tag,)

class SubscriptDesignator(object):
    def __init__(self, d):
        self.subscript = DoExpression(d['subscript'])
    def __str__(self):
        return '[%s]' % (self.subscript,)

def Designator(d):
    if d.get('member') is not None:
        return MemberDesignator(d['member'])
    if d.get('array') is not None:
        return SubscriptDesignator(d['array'])
    raise UnhandledEntity(d)

class DesignatedInitialiser(object):
    def __init__(self, di):
        self.d = [Designator(d) for d in di.get('designation', [])]
        self.i = Initialiser(di['initialiser'])
    def __str__(self):
        if self.d:
            return '%s = %s' % (' '.join(map(str, self.d)), self.i)
        return str(self.i)

class InitList(object):
    def __init__(self, ilist):
        self.list = [DesignatedInitialiser(di) for di in ilist]
    def __str__(self):
        return ', '.join(map(str, self.list))

def Initialiser(init):
    # <initialiser>   ::= <expression> | '{' <init-list> ','? '}'
    if init.get('init_list') is not None:
        return InitList(init['init_list'])
    return DoAssign(init)

class Declaration(object):
    # <object-decl>   ::= <decl-spec> ('=' <initialiser>)?
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
                self.sc = Static
            elif self.sc.get('extern') is not None:
                self.sc = Extern
            elif self.sc.get('auto') is not None:
                self.sc = Auto
            else:
                raise UnhandledEntity(self.sc)
        self.typ = get_type(declare['type'])
        if self.typ is None:
            raise UnhandledEntity(declare['type'])
        if declare.get('qualifier_list') is not None:
            self.typ = build_qualifiers(declare['qualifier_list'], self.typ)
        # <declaration>   ::= <object-decls> ';' | <function-defn>
        # <object-decls>  ::= <object-decl> (',' <object-decls>)?
        self.declarations = [Declaration(d, self.sc, self.typ) for d in declare['declaration']]
    def __str__(self):
        if not self.declarations:
            return 'mention %s;' % (self.typ,)
        return ' '.join(['declare %s;'%(d,) for d in self.declarations])

class ReturnStatement(object):
    def __init__(self, rs):
        self.value = rs.get('value')
        if self.value is not None:
            self.value = DoExpression(self.value)
    def __str__(self):
        if self.value is None:
            return 'return;'
        return 'return %s;' % (self.value,)

class ExpressionStatement(object):
    def __init__(self, es):
        self.expr = DoExpression(es)
    def __str__(self):
        return str(self.expr) + ';'

class LabelStatement(object):
    def __init__(self, ls):
        self.label = ls['label']
    def __str__(self):
        return self.label + ':'

class IfStatement(object):
    def __init__(self, ifs):
        self.condition = DoExpression(ifs['condition'])
        self.true = Statement(ifs['true'])
        self.false = ifs.get('false')
        if self.false is not None:
            self.false = Statement(self.false)
    def __str__(self):
        if self.false is None:
            el = ''
        else:
            el = ' else %s' % (self.false,)
        return 'if (%s) %s%s'%(self.condition, self.true, el)

class GotoStatement(object):
    def __init__(self, gs):
        self.label = gs['label']
    def __str__(self):
        return 'goto %s;' % (self.label,)

def Statement(stmt):
    if stmt.get('return_stmt') is not None:
        return ReturnStatement(stmt['return_stmt'])
    if stmt.get('expr_stmt') is not None:
        return ExpressionStatement(stmt['expr_stmt'])
    if stmt.get('label_stmt') is not None:
        return LabelStatement(stmt['label_stmt'])
    if stmt.get('if_stmt') is not None:
        return IfStatement(stmt['if_stmt'])
    if stmt.get('goto_stmt') is not None:
        return GotoStatement(stmt['goto_stmt'])
    raise UnhandledEntity(stmt)

class BlockStatement(object):
    def __init__(self, block):
        decls = block.get('declare_list', [])
        self.decls = [Declare(decl) for decl in decls]
        stmts = block.get('stmt_list', [])
        self.stmts = [Statement(stmt) for stmt in stmts]
    def __str__(self):
        return ' '.join(map(str, ['{'] + self.decls + self.stmts + ['}']))

class FunctionDefn(object):
    # <function-defn> ::= <storage-class>? <qualifier-list>? <type> <decl_spec> <block-stmt>
    def __init__(self, defn):
        self.sc = defn.get('storage_class')
        if self.sc is not None:
            if self.sc.get('static') is not None:
                self.sc = Static
            elif self.sc.get('extern') is not None:
                self.sc = Extern
            elif self.sc.get('auto') is not None:
                self.sc = Auto
            else:
                raise UnhandledEntity(self.sc)
        if defn.get('qualifier_list') is not None:
            raise UnhandledEntity(defn['qualifier_list'])
        self.typ = get_type(defn['type'])
        if self.typ is None:
            raise UnhandledEntity(defn['type'])
        self.decl_spec = DeclSpec(defn['decl_spec'], self.typ)
        if not isinstance(self.decl_spec.object.typ, Function):
            raise ASTError("FunctionDefn has type", self.decl_spec.object.typ)
        self.body = BlockStatement(defn)
    def __str__(self):
        s = str(self.decl_spec)
        if self.sc is not None:
            s = '%s %s' % (self.sc, s)
        return 'define %s body %s' % (s, self.body)

class AST_builder(object):
    def __init__(self, parse_tree):
        self.decls = []
        for entity in parse_tree:
            if entity.get('declare'):
                self.decls.append(Declare(entity['declare']))
            elif entity.get('function_defn'):
                self.decls.append(FunctionDefn(entity['function_defn']))
            else:
                raise UnhandledEntity(entity)

## Test code

if __name__ == "__main__":
    if len(sys.argv) > 1:
        with open(sys.argv[1], 'r') as f:
            source = f.read()
    else:
        source = sys.stdin.read()
    parse_tree = parser.parse(source)
    print "Parse tree:"
    print parse_tree.dump()
    print
    ast = AST_builder(parse_tree)
    for decl in ast.decls:
        print decl

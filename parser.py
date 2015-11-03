#!/usr/bin/python

import re, sys, pprint

## Lexer - splits input string into token stream

class LexError(Exception): pass

class Lexer(object):
    class Token(object):
        RE = None
        def __init__(self, raw):
            self.raw = raw
        def __str__(self):
            return self.raw
        def __repr__(self):
            return '<%s:%s>'%(self.__class__.__name__, self.raw)

    class Identifier(Token):
        RE = r'[_a-zA-Z]\w*'

    class Keyword(Token): pass
    class StorageClass(Keyword): pass
    class Auto(StorageClass):
        RE = 'auto'
    class Static(StorageClass):
        RE = 'static'
    class Extern(StorageClass):
        RE = 'extern'
    class Const(Keyword):
        RE = 'const'
    class Return(Keyword):
        RE = 'return'
    class Struct(Keyword):
        RE = 'struct'
    class BuiltinType(Keyword): pass
    class Void(BuiltinType):
        RE = 'void'
    class Bool(BuiltinType):
        RE = 'bool'
    class Byte(BuiltinType):
        RE = 'byte'
    class Word(BuiltinType):
        RE = 'word'
    class If(Keyword):
        RE = 'if'
    class Goto(Keyword):
        RE = 'goto'

    class Whitespace(Token):
        RE = r'\s'

    class LParen(Token):
        RE = r'\('

    class RParen(Token):
        RE = r'\)'

    class LBracket(Token):
        RE = r'\['

    class RBracket(Token):
        RE = r'\]'

    class LBrace(Token):
        RE = r'\{'

    class RBrace(Token):
        RE = r'\}'

    class Star(Token):
        RE = r'\*'

    class Hash(Token):
        RE = r'#'

    class Comma(Token):
        RE = r','

    class Colon(Token):
        RE = r':'

    class Semicolon(Token):
        RE = r';'

    class Comment(Token): pass

    class CommentToEOL(Comment):
        RE = r'//[^\n]*'

    class WingedComment(Comment):
        # We could do this without non-greedy matching, but it would involve the
        # following line-noise regex: r'/\*/?\**(?:[^*/][^*]*\*?)*\*/'
        RE = r'(?s)/\*.*?\*/'

    class Comparator(Token): pass
    class Equal(Comparator):
        RE = r'=='
    class NotEqual(Comparator):
        RE = r'!='
    class LessThan(Comparator):
        RE = r'<'
    class LessOrEqual(Comparator):
        RE = r'<='
    class GreaterThan(Comparator):
        RE = r'>'
    class GreaterOrEqual(Comparator):
        RE = r'>='

    class AssignIsh(Token): pass
    class Assignment(AssignIsh):
        RE = r'='
    class Add(AssignIsh):
        RE = r'\+='
    class Subtract(AssignIsh):
        RE = r'-='

    class Mutate(Token): pass
    class Incr(Mutate):
        RE = r'\+\+'
    class Decr(Mutate):
        RE = r'--'

    class Not(Token):
        RE = r'!'

    class Dot(Token):
        RE = r'\.'

    class Memb(Token):
        RE = r'->'

    class Number(Token): pass
    class LiteralDec(Number):
        RE = r'[1-9][0-9]*'
        def __init__(self, raw):
            super(Lexer.LiteralDec, self).__init__(raw)
            self.value = int(raw, 10)
    class LiteralHex(Number):
        RE = r'0x[0-9a-fA-F]+'
        def __init__(self, raw):
            super(Lexer.LiteralHex, self).__init__(raw)
            self.value = int(raw, 16)
    class LiteralOct(Number):
        # Notice the slight oddity that 0 is an octal, rather than a decimal, literal.
        # It makes no difference, as it's the same number either way
        RE = r'0[0-7]*'
        def __init__(self, raw):
            super(Lexer.LiteralOct, self).__init__(raw)
            self.value = int(raw, 8)
    class LongNumber(Number): pass
    class LongDec(LongNumber):
        RE = r'[1-9][0-9]*[lL]'
        def __init__(self, raw):
            super(Lexer.LongDec, self).__init__(raw)
            self.value = int(raw[:-1], 10)
    class LongHex(LongNumber):
        RE = r'0x[0-9a-fA-F]+[lL]'
        def __init__(self, raw):
            super(Lexer.LongHex, self).__init__(raw)
            self.value = int(raw[:-1], 16)
    class LongOct(LongNumber):
        # Notice the slight oddity that 0 is an octal, rather than a decimal, literal.
        # It makes no difference, as it's the same number either way
        RE = r'0[0-7]*[lL]'
        def __init__(self, raw):
            super(Lexer.LongOct, self).__init__(raw)
            self.value = int(raw[:-1], 8)

    class String(Token):
        RE = r'"(?:[^"]|\\")*"'
        def __init__(self, raw):
            super(Lexer.String, self).__init__(raw)
            self.str = raw[1:-1]

    tokens = [Identifier, Auto, Static, Extern, Const, Return,
              Struct, Void, Bool, Byte, Word, If, Goto,
              Whitespace, LParen, RParen, LBracket, RBracket, LBrace, RBrace,
              Star, Hash, Comma, Colon, Semicolon,
              CommentToEOL, WingedComment,
              Assignment, Add, Subtract, Incr, Decr, Not, Dot, Memb,
              Equal, NotEqual, LessThan, LessOrEqual, GreaterThan, GreaterOrEqual,
              LiteralDec, LiteralHex, LiteralOct, LongDec, LongHex, LongOct, String]

    def __init__(self):
        self.tres = [(t, re.compile(t.RE)) for t in self.tokens]
    
    def lex(self, source):
        out = []
        while source:
            matches = [(t, r.match(source)) for (t, r) in self.tres]
            choices = [(t, m.group(0)) for (t, m) in matches if m is not None]
            # Keyword subsumes Identifier
            if any(issubclass(t, self.Keyword) for (t, r) in choices):
                choices = [(t, r) for (t, r) in choices if not issubclass(t, self.Identifier)]
            maxlen = max(len(r) for (t, r) in choices)
            longest = [(t, r) for (t, r) in choices if len(r) == maxlen]
            assert longest
            if len(longest) > 1:
                raise LexError("Ambiguous lex", longest)
            token, raw = longest[0]
            out.append(token(raw))
            source = source[len(raw):]
        return out

    @classmethod
    def prune(cls, tokens):
        return [t for t in tokens if not isinstance(t, cls.Whitespace) and not isinstance(t, cls.Comment)]

## Parser - builds token stream into parse tree and related gubbins (e.g. type, struct and identifier decls)

class ParseError(Exception): pass
class NestedFunction(ParseError): pass
class NotDeclaration(ParseError): pass

def show_error_location(tokens):
    words = [getattr(t, 'raw', t) for t in tokens]
    out = words.pop(0)
    while words and len(out) + len(words[0]) + 1 < 76:
        out += ' ' + words.pop(0)
    if words:
        out = out[:-3] + '...'
    return out

class Parser(object):
    class Declarator(object):
        def __init__(self, name):
            self.name = name
        def __repr__(self):
            return '%s()'%(self.__class__.__name__)
        def __eq__(self, other):
            return False
        def __ne__(self, other):
            return not (self == other)
    class ValueOfType(Declarator): # the thing that has the type that started the declaration
        def __init__(self, typ):
            self.typ = typ
        def __repr__(self):
            return 'ValueOfType(%s)'%(self.typ,)
        def __eq__(self, other):
            return isinstance(other, Parser.ValueOfType) and self.typ == other.typ
    class Identifier(Declarator): # does not escape into type definitions
        def __repr__(self):
            return 'Identifier(%s)'%(self.name,)
    class Pointer(Declarator):
        def __init__(self, pointee):
            self.pointee = pointee
        def __repr__(self):
            return 'Pointer(%r)'%(self.pointee,)
        def __eq__(self, other):
            return isinstance(other, Parser.Pointer) and self.pointee == other.pointee
    class Array(Declarator):
        def __init__(self, pointee, n):
            self.pointee = pointee
            self.n = n
        def __repr__(self):
            return 'Array(%r, %r)'%(self.pointee, self.n)
        def __eq__(self, other):
            return isinstance(other, Parser.Array) and self.pointee == other.pointee and self.n == other.n
    class ParenDecl(Declarator): # does not escape into type definitions
        def __init__(self, contents):
            self.contents = contents
        def __repr__(self):
            return 'ParenDecl(%r)'%(self.contents,)
    class FunctionDecl(Declarator):
        def __init__(self, bound, arglist):
            self.bound = bound
            self.arglist = arglist
        def __repr__(self):
            return 'FunctionDecl(%r, %r)'%(self.bound, self.arglist)
        def __eq__(self, other):
            return isinstance(other, Parser.FunctionDecl) and self.arglist == other.arglist
    class ArgList(Declarator):
        def __init__(self, args):
            self.args = args
        def __repr__(self):
            return 'ArgList(%r)'%(self.args,)
        def __eq__(self, other):
            if not isinstance(other, Parser.ArgList) and len(self.args) == len(other.args): return False
            for s, o in zip(self.args, other.args):
                if s[1] != o[1]: return False # only compare types, not names
            return True
    class Expression(object): pass
    class Literal(Expression):
        def __init__(self, value):
            if value > 255 or value < -128:
                raise ParseError("Value out of range for literal", value)
            self.value = value
        def __repr__(self):
            return 'Literal(%d)'%(self.value,)
        def __eq__(self, other):
            return isinstance(other, Parser.Literal) and self.value == other.value
    class LongLiteral(Expression):
        def __init__(self, value):
            if value > 65535 or value < -32768:
                raise ParseError("Value out of range for long literal", value)
            self.value = value
        def __repr__(self):
            return 'LongLiteral(%d)'%(self.value,)
        def __eq__(self, other):
            return isinstance(other, Parser.LongLiteral) and self.value == other.value
    class StringLiteral(Expression):
        def __init__(self, value):
            self.value = value
        def __repr__(self):
            return 'StringLiteral(%r)'%(self.value,)
    class IdentifierExpression(Expression):
        def __init__(self, name):
            self.name = name
        def __repr__(self):
            return 'IdentifierExpression(%s)'%(self.name,)
    class BinaryOp(Expression):
        def __init__(self, op, left, right):
            self.op = op
            self.left = left
            self.right = right
        def __repr__(self):
            return '%s(%s, %r, %r)'%(self.__class__.__name__, self.op, self.left, self.right)
    class Comparison(BinaryOp): pass
    class AssignIsh(BinaryOp): pass
    class UnaryOp(Expression):
        def __init__(self, op, erand):
            self.op = op
            self.erand = erand
        def __repr__(self):
            return '%s(%s, %r)'%(self.__class__.__name__, self.op, self.erand)
    class Dereference(UnaryOp): pass
    class Precrement(UnaryOp): pass
    class Postcrement(UnaryOp): pass
    class FunctionCall(Expression):
        def __init__(self, func, args):
            self.func = func
            self.args = args
        def __repr__(self):
            return 'FunctionCall(%r, %r)'%(self.func, self.args)
    class Statement(object): pass
    class BlockStatement(Statement):
        def __init__(self, local, body):
            self.local = local
            self.body = body
        def __repr__(self):
            return 'BlockStatement(%r, %r)'%(self.local, self.body)
    class ExpressionStatement(Statement):
        def __init__(self, expr):
            self.expr = expr
        def __repr__(self):
            return 'ExpressionStatement(%r)'%(self.expr,)
    class ReturnStatement(Statement):
        def __init__(self, expr):
            self.expr = expr
        def __repr__(self):
            return 'ReturnStatement(%r)'%(self.expr,)
    class Label(Statement):
        def __init__(self, name):
            self.name = name
        def __repr__(self):
            return 'Label(%s)'%(self.name,)
    class IfStatement(Statement):
        def __init__(self, cond, then):
            self.cond = cond
            self.then = then
        def __repr__(self):
            return 'IfStatement(%r, %r)'%(self.cond, self.then)
    class GotoStatement(Statement):
        def __init__(self, label):
            self.label = label
        def __repr__(self):
            return 'GotoStatement(%s)'%(self.label,)
    def __init__(self, **options):
        self.structs = []
        self.globals = []
        self.options = options
    def expected(self, what, tokens, exc=ParseError):
        if not tokens: # we should always at least get our end-marker
            raise exc("Impossible: expected %s, got nothing!"%(what,))
        if tokens[0] == '$': # end-marker
            self.eof(what, exc=exc)
        raise exc("Expected %s, got:\n    %s"%(what, show_error_location(tokens),))
    def eof(self, what, exc=ParseError):
        raise exc("Expected %s, got EOF"%(what,))
    def parse(self, tokens):
        self.parse_file_scope(tokens + ['$'])
    def parse_file_scope(self, tokens):
        # [storage] type [declarator [= initialiser] [, declarator [= initialiser] [...]]]; // global variable declarations, including function declaration without definition
        # [storage] type declarator { local-variables function-body } // function definition
        while tokens[0] != '$':
            for declaration in self.parse_declaration(tokens, allowfunc=True):
                self.globals.append(declaration)
    def parse_declaration(self, tokens, allowfunc=False):
        sclass = None
        if isinstance(tokens[0], Lexer.StorageClass):
            sclass = tokens.pop(0)
        if isinstance(tokens[0], Lexer.Struct):
            raise ParseError("struct not yet supported!")
        if isinstance(tokens[0], Lexer.BuiltinType):
            typ = tokens.pop(0).raw
        elif sclass is not None:
            self.expected("type", tokens)
        else:
            self.expected("type", tokens, exc=NotDeclaration)
        while True:
            if isinstance(tokens[0], Lexer.Semicolon):
                tokens.pop(0)
                break
            name, decl = self.parse_declarator(tokens, typ)
            func = isinstance(decl, self.FunctionDecl)
            if func and isinstance(tokens[0], Lexer.LBrace):
                if not allowfunc:
                    raise NestedFunction("Nested function at:\n    %s"%(show_error_location(tokens),))
                tokens.pop(0)
                body = self.parse_function_body(tokens)
                yield (name, sclass, decl, body)
                break
            else:
                initial = None
                if isinstance(tokens[0], Lexer.Assignment) and not func:
                    tokens.pop(0)
                    initial = self.parse_expression(tokens)
                if isinstance(tokens[0], Lexer.Semicolon):
                    yield (name, sclass, decl, initial)
                    continue
                if isinstance(tokens[0], Lexer.Comma):
                    yield (name, sclass, decl, initial)
                    tokens.pop(0)
                    continue
                self.expected("initialiser, ',' or ';'", tokens)
    def parse_local_variables(self, tokens):
        local = []
        while True:
            try:
                for declaration in self.parse_declaration(tokens, allowfunc=False):
                    local.append(declaration)
            except NotDeclaration:
                break
        return local
    def parse_statement(self, tokens):
        if isinstance(tokens[0], Lexer.Keyword):
            if isinstance(tokens[0], Lexer.Return):
                tokens.pop(0)
                expr = self.parse_expression(tokens)
                if isinstance(tokens[0], Lexer.Semicolon):
                    tokens.pop(0)
                else:
                    self.expected("';' after expression", tokens)
                return self.ReturnStatement(expr)
            if isinstance(tokens[0], Lexer.If):
                tokens.pop(0)
                if isinstance(tokens[0], Lexer.LParen):
                    tokens.pop(0)
                else:
                    self.expected("'(' after 'if'", tokens)
                expr = self.parse_expression(tokens)
                if isinstance(tokens[0], Lexer.RParen):
                    tokens.pop(0)
                else:
                    self.expected("')' after condition", tokens)
                if isinstance(tokens[0], Lexer.LBrace):
                    tokens.pop(0)
                    stmt = self.parse_function_body(tokens)
                else:
                    stmt = self.parse_statement(tokens)
                return self.IfStatement(expr, stmt)
            if isinstance(tokens[0], Lexer.Goto):
                tokens.pop(0)
                if isinstance(tokens[0], Lexer.Identifier):
                    label = tokens.pop(0)
                else:
                    self.expected("label after goto")
                if isinstance(tokens[0], Lexer.Semicolon):
                    tokens.pop(0)
                else:
                    self.expected("';' after 'goto %s'"%(label,))
                return self.GotoStatement(label)
            self.expected("a keyword implemented", tokens)
        if isinstance(tokens[0], Lexer.Identifier) and isinstance(tokens[1], Lexer.Colon):
            label = tokens.pop(0)
            tokens.pop(0)
            if label.raw[0] == '_': # if they ever use "_genlabel" bad things will happen...
                self.warn("Labels beginning with _ are reserved for the implementation.")
            return self.Label(label)
        expr = self.parse_expression(tokens)
        if isinstance(tokens[0], Lexer.Semicolon):
            tokens.pop(0)
        else:
            self.expected("';' after expression", tokens)
        return self.ExpressionStatement(expr)
    def parse_statement_list(self, tokens):
        stmts = []
        while True:
            if isinstance(tokens[0], Lexer.RBrace):
                tokens.pop(0)
                return stmts
            stmts.append(self.parse_statement(tokens))
    def parse_function_body(self, tokens):
        local = self.parse_local_variables(tokens)
        body = self.parse_statement_list(tokens)
        return self.BlockStatement(local, body)
    def parse_expression(self, tokens, context=None):
        left = None
        if isinstance(tokens[0], Lexer.LongNumber):
            left = self.LongLiteral(tokens.pop(0).value)
        elif isinstance(tokens[0], Lexer.Number):
            left = self.Literal(tokens.pop(0).value)
        elif isinstance(tokens[0], Lexer.String):
            left = self.StringLiteral(tokens.pop(0).str)
        elif isinstance(tokens[0], Lexer.Identifier):
            left = self.IdentifierExpression(tokens.pop(0).raw)
        elif isinstance(tokens[0], Lexer.Star):
            op = tokens.pop(0)
            pointee = self.parse_expression(tokens, context=self.Dereference)
            left = self.Dereference(op, pointee)
        elif isinstance(tokens[0], Lexer.Mutate):
            mu = tokens.pop(0)
            operand = self.parse_expression(tokens)
            left = self.Precrement(mu, operand)
        else:
            self.expected("expression", tokens)
        if isinstance(tokens[0], Lexer.LParen):
            tokens.pop(0)
            args = self.parse_argument_list(tokens)
            left = self.FunctionCall(left, args)
        if isinstance(tokens[0], Lexer.Mutate):
            mu = tokens.pop(0)
            left = self.Postcrement(mu, left)
        if context == self.Dereference:
            return left
        if isinstance(tokens[0], Lexer.Comparator):
            comp = tokens.pop(0)
            right = self.parse_expression(tokens)
            return self.Comparison(comp, left, right)
        if isinstance(tokens[0], Lexer.AssignIsh):
            ai = tokens.pop(0)
            right = self.parse_expression(tokens)
            return self.AssignIsh(ai, left, right)
        return left
    def parse_left_declarator(self, tokens, typespec=False):
        # <nothing> // only in type-specifiers
        # identifier
        # ( declarator )
        # * declarator
        # qualifier declarator
        if isinstance(tokens[0], Lexer.Identifier):
            return self.Identifier(tokens.pop(0).raw)
        if isinstance(tokens[0], Lexer.Star):
            tokens.pop(0)
            return self.Pointer(self.parse_left_declarator(tokens, typespec=typespec))
        if isinstance(tokens[0], Lexer.LParen):
            tokens.pop(0)
            contents = self.parse_right_declarator(tokens, typespec=typespec)
            if isinstance(tokens[0], Lexer.RParen):
                tokens.pop(0)
                return self.ParenDecl(contents)
            self.expected(')', tokens)
        if typespec:
            return None
        self.expected("declarator", tokens)
    def parse_right_declarator(self, tokens, typespec=False):
        # left-declarator
        # declarator ( argument-or-type-list )
        decl = self.parse_left_declarator(tokens, typespec=typespec)
        if decl:
            if isinstance(tokens[0], Lexer.LParen):
                tokens.pop(0)
                arglist = self.parse_parameter_list(tokens)
                return self.FunctionDecl(decl, arglist)
        return decl
    def parse_declarator(self, tokens, typ, typespec=False):
        def invert_declarator(bwd, fstack, fwd):
            if isinstance(bwd, Parser.Identifier):
                while fstack:
                    f = fstack.pop(-1)
                    fwd = Parser.FunctionDecl(fwd, f)
                return (bwd.name, fwd)
            if isinstance(bwd, Parser.Pointer):
                fwd = Parser.Pointer(fwd)
                return invert_declarator(bwd.pointee, fstack, fwd)
            if isinstance(bwd, Parser.FunctionDecl):
                fstack.append(bwd.arglist)
                return invert_declarator(bwd.bound, fstack, fwd)
            if isinstance(bwd, Parser.ParenDecl):
                if fstack:
                    f = fstack.pop(-1)
                    fwd = Parser.FunctionDecl(fwd, f)
                return invert_declarator(bwd.contents, fstack, fwd)
            if bwd is None: return None, fwd
            raise ParseError("Unrecognised Declarator", bwd)
        backward = self.parse_right_declarator(tokens, typespec=typespec)
        fstack = []
        name, forward = invert_declarator(backward, fstack, self.ValueOfType(typ))
        return name, forward
    def parse_parameter_list(self, tokens):
        args = []
        while True:
            if isinstance(tokens[0], Lexer.RParen):
                tokens.pop(0)
                return self.ArgList(args)
            if isinstance(tokens[0], Lexer.BuiltinType):
                typ = tokens.pop(0).raw
            else:
                self.expected("type or ')'", tokens)
            name, arg = self.parse_declarator(tokens, typ, typespec=True)
            args.append((name, arg))
            if isinstance(tokens[0], Lexer.RParen): continue
            if isinstance(tokens[0], Lexer.Comma):
                tokens.pop(0)
                continue
            self.expected("',' or ')'", tokens)
    def parse_argument_list(self, tokens):
        args = []
        while True:
            if isinstance(tokens[0], Lexer.RParen):
                tokens.pop(0)
                return self.ArgList(args)
            args.append(self.parse_expression(tokens))
            if isinstance(tokens[0], Lexer.RParen): continue
            if isinstance(tokens[0], Lexer.Comma):
                tokens.pop(0)
                continue
            self.expected("',' or ')'", tokens)
    def warn(self, text):
        print >>sys.stderr, text

## Entry point

def parse(source):
    tokens = Lexer().lex(source)
    pruned_tokens = Lexer.prune(tokens)
    parser = Parser()
    parser.parse(pruned_tokens)
    return parser

## Test code

if __name__ == "__main__":
    if len(sys.argv) > 1:
        with open(sys.argv[1], 'r') as f:
            source = f.read()
    else:
        source = sys.stdin.read()
    tokens = Lexer().lex(source)
    pruned_tokens = Lexer.prune(tokens)
    print ' '.join(map(str, pruned_tokens))
    print
    parser = Parser()
    try:
        parser.parse(pruned_tokens)
    finally:
        print "Final globals:"
        pprint.pprint(parser.globals)

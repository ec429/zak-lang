#!/usr/bin/python

import sys, pprint
import parser
LEX = parser.Lexer
PAR = parser.Parser

## Convert parse tree to Two-Address Code intermediate form

class TACError(Exception): pass

class TACifier(object):
    class TACStatement(object): pass
    class TACDeclare(TACStatement):
        def __init__(self, name, sc, typ):
            self.name = name
            self.sc = sc
            self.typ = typ
        def rename(self, dst, src):
            raise NotImplementedError()
        def __repr__(self):
            return 'TACDeclare(%r, %r, %r)'%(self.name, self.sc, self.typ)
    class TACRename(TACStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def __repr__(self):
            return 'TACRename(%r, %r)'%(self.dst, self.src)
    class TACDeref(TACStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.src == dst:
                self.src = src
        def __repr__(self):
            return 'TACDeref(%r, %r)'%(self.dst, self.src)
    class TACAssign(TACStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.src == dst:
                self.src = src
        def __repr__(self):
            return 'TACAssign(%r, %r)'%(self.dst, self.src)
    class TACAdd(TACStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.src == dst:
                self.src = src
        def __repr__(self):
            return 'TACAdd(%r, %r)'%(self.dst, self.src)
    class TACReturn(TACStatement):
        def __init__(self, src):
            self.src = src
        def rename(self, dst, src):
            if self.src == dst:
                self.src = src
        def __repr__(self):
            return 'TACReturn(%r)'%(self.src,)
    class Value(object):
        def __init__(self, typ):
            self.typ = typ
        def __repr__(self):
            return 'Value(%r)'%(self.typ,)
    class Identifier(Value):
        def __init__(self, typ, name):
            super(TACifier.Identifier, self).__init__(typ)
            self.name = name
        def rename(self, dst, src):
            if self.name == dst:
                self.name = src
        def __repr__(self):
            return 'Identifier(%r, %r)'%(self.typ, self.name)
    class Gensym(object):
        def __init__(self, n):
            self.n = n
        def __repr__(self):
            return '$(%d)'%(self.n,)
    def gensym(self):
        n = self.gennum
        self.gennum += 1
        return self.Gensym(n)
    def __init__(self):
        self.scopes = [{}]
        self.functions = {None:[]}
        self.in_func = None
        self.gennum = 0
    def arg_list(self, arglist):
        scope = {}
        for name,typ in arglist.args:
            if name in scope:
                raise TACError("Name", name, "redeclared within parameter list")
            scope[name] = (LEX.Auto("auto"), typ)
        return scope
    def get_lvalue(self, lval):
        if isinstance(lval, PAR.IdentifierExpression):
            for scope in reversed(self.scopes):
                if lval.name in scope:
                    sc, typ = scope[lval.name]
                    return (self.Identifier(typ, lval.name), [])
            raise TACError("Name", lval.name, "not in scope")
        pprint.pprint(lval)
        raise NotImplementedError()
    def get_rvalue(self, rval):
        if isinstance(rval, PAR.IdentifierExpression):
            for scope in reversed(self.scopes):
                if rval.name in scope:
                    sc, typ = scope[rval.name]
                    return (self.Identifier(typ, rval.name), [])
            raise TACError("Name", rval.name, "not in scope")
        if isinstance(rval, PAR.Dereference):
            pointee, ps = self.get_rvalue(rval.erand)
            if not isinstance(pointee.typ, PAR.Pointer):
                raise TACError("Dereferencing non-pointer", rval.erand)
            sym = self.gensym()
            typ = pointee.typ.pointee
            self.scopes[-1][sym] = (LEX.Auto('auto'), typ)
            stmts = ps
            stmts.append(self.TACDeclare(sym, LEX.Auto('auto'), typ))
            stmts.append(self.TACDeref(sym, pointee.name))
            return (self.Identifier(typ, sym), stmts)
        pprint.pprint(rval)
        raise NotImplementedError()
    def emit_assignish(self, op, lvalue, rvalue):
        if isinstance(lvalue, self.Identifier):
            if isinstance(rvalue, self.Identifier):
                if lvalue.typ != rvalue.typ:
                    raise TACError("Type mismatch assigning", rvalue, "to", lvalue)
                if isinstance(op, LEX.Add):
                    return [self.TACAdd(lvalue.name, rvalue.name)]
                raise NotImplementedError(op)
            raise TACError("Uninterpreted rvalue", rvalue)
        raise TACError("Uninterpreted lvalue", lvalue)
    def emit_return(self, rvalue):
        if self.in_func is None:
            raise TACError("return outside function")
        decl = self.in_func[1]
        typ = decl.bound
        if isinstance(rvalue, self.Identifier):
            if typ != rvalue.typ:
                raise TACError("Type mismatch returning", rvalue, "from", decl)
            return [self.TACReturn(rvalue.name)]
        raise TACError("Uninterpreted rvalue", rvalue)
        raise NotImplementedError()
    def walk_expr(self, expr):
        if isinstance(expr, PAR.IdentifierExpression):
            return self.get_rvalue(expr)
        if isinstance(expr, PAR.AssignIsh):
            op = expr.op
            lval = expr.left
            rval = expr.right
            lvalue, ls = self.get_lvalue(lval)
            rvalue, rs = self.get_rvalue(rval)
            return (lvalue, rs + self.emit_assignish(op, lvalue, rvalue) + ls) # lvalue becomes an rvalue
        pprint.pprint(expr)
        raise NotImplementedError()
    def walk_stmt(self, stmt):
        if isinstance(stmt, PAR.ExpressionStatement):
            _, stmts = self.walk_expr(stmt.expr)
            return stmts
        elif isinstance(stmt, PAR.ReturnStatement):
            rvalue, stmts = self.walk_expr(stmt.expr)
            return stmts + self.emit_return(rvalue)
        else:
            pprint.pprint(stmt)
            raise NotImplementedError()
    def declare(self, declaration):
        stmts = []
        name, sc, decl, init = declaration
        if name in self.scopes[-1]:
            raise TACError("Identifier", name, "redefined in same scope")
        self.scopes[-1][name] = (sc, decl)
        rvalue, rs = self.get_rvalue(init)
        stmts.extend(rs)
        if not isinstance(rvalue, self.Identifier):
            raise TACError("Uninterpreted rvalue", rvalue)
        if isinstance(rvalue.name, self.Gensym):
            stmts.append(self.TACRename(name, rvalue))
        else:
            stmts.insert(0, self.TACDeclare(name, sc, decl))
            stmts.append(self.TACAssign(name, rvalue))
        return stmts
    def walk(self, block):
        func = []
        for declaration in block.local:
            func.extend(self.declare(declaration))
        for stmt in block.body:
            func.extend(self.walk_stmt(stmt))
        return func
    def normalise(self, func):
        # Hoick all Declares to the beginning, and apply any Renames
        declares = [t for t in func if isinstance(t, self.TACDeclare)]
        renames = [t for t in func if isinstance(t, self.TACRename)]
        the_rest = [t for t in func if not isinstance(t, (self.TACDeclare, self.TACRename))]
        for rename in renames:
            for declare in declares:
                if declare.name == rename.src.name:
                    if declare.typ != rename.src.typ:
                        raise TACError("Type mismatch normalising", rename, "on", declare)
                    declare.name = rename.dst
                    break
            else:
                raise TACError("Found no TACDeclare matching", rename)
            for t in the_rest:
                t.rename(rename.src.name, rename.dst)
        return declares + the_rest
    def add(self, name, sc, decl, init):
        if isinstance(decl, PAR.FunctionDecl) and isinstance(init, PAR.BlockStatement):
            if isinstance(sc, LEX.Extern):
                raise TACError("extern function with definition")
            if self.in_func is not None: # should be impossible, parser won't allow it
                raise TACError("Nested function definition")
            self.in_func = (name, decl)
            self.scopes.append(self.arg_list(decl.arglist))
            func = self.walk(init)
            self.scopes.pop(-1)
            self.in_func = None
            self.functions[name] = self.normalise(func)
            self.scopes[-1][name] = (sc, decl)
        else:
            raise NotImplementedError()

## Entry point
def tacify(parse_tree):
    tac = TACifier()
    for (name, sc, decl, init) in parse_tree.globals:
        tac.add(name, sc, decl, init)
    return tac

## Test code

if __name__ == "__main__":
    if len(sys.argv) > 1:
        with open(sys.argv[1], 'r') as f:
            source = f.read()
    else:
        source = sys.stdin.read()
    parse_tree = parser.parse(source)
    print "Parse globals:"
    pprint.pprint(parse_tree.globals)
    print
    tac = TACifier()
    for (name, sc, decl, init) in parse_tree.globals:
        tac.add(name, sc, decl, init)
    print "TAC scopes:"
    pprint.pprint(tac.scopes)
    print "TAC functions:"
    pprint.pprint(tac.functions)
    assert tac.in_func is None, tac.in_func
    assert len(tac.scopes) == 1

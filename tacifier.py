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
            if self.name == dst:
                raise TACError("Tried to rename", self, "to", src)
        def __repr__(self):
            return 'TACDeclare(%r, %r, %r)'%(self.name, self.sc, self.typ)
    class TACInitGlobal(TACStatement):
        def __init__(self, name, value):
            self.name = name
            self.value = value
        def rename(self, dst, src):
            raise NotImplementedError()
        def __repr__(self):
            return 'TACInitGlobal(%r, %r)'%(self.name, self.value)
    class TACRename(TACStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def rename(self, dst, src):
            # I don't know if this should be allowed.  But hopefully not.
            raise TACError("Tried to rename(%r, %r, %r)"%(self, dst, src))
        def __repr__(self):
            return 'TACRename(%r, %r)'%(self.dst, self.src)
    class TACDeref(TACStatement): # read through a pointer
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
    class TACWrite(TACStatement): # write through a pointer
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.src == dst:
                self.src = src
        def __repr__(self):
            return 'TACWrite(%r, %r)'%(self.dst, self.src)
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
    class TACCompare(TACStatement):
        def __init__(self, op, left, right):
            self.op = op.raw
            self.left = left
            self.right = right
        def rename(self, dst, src):
            if self.left == dst:
                self.left = src
            if self.right == dst:
                self.right = src
        def __repr__(self):
            return 'TACCompare(%s, %r, %r)'%(self.op, self.left, self.right)
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
    class TACCall(TACStatement):
        def __init__(self, func, ret, args):
            self.func = func
            self.ret = ret
            self.args = args
        def rename(self, dst, src):
            if self.func == dst:
                self.func = src
            if self.ret == dst:
                self.ret = src
            for arg in self.args: # (sym, stmts)
                if arg[0] == dst:
                    arg[0] = src
                for t in arg[1]:
                    t.rename(dst, src)
        def __repr__(self):
            return 'TACCall(%r, %r, %r)'%(self.func, self.ret, self.args)
    class TACReturn(TACStatement):
        def __init__(self, src):
            self.src = src
        def rename(self, dst, src):
            if self.src == dst:
                self.src = src
        def __repr__(self):
            return 'TACReturn(%r)'%(self.src,)
    class TACLabel(TACStatement):
        def __init__(self, name):
            self.name = name
        def rename(self, dst, src): pass # nothing to do
        def __repr__(self):
            return 'TACLabel(%s)'%(self.name,)
    class TACGoto(TACStatement):
        def __init__(self, label):
            self.label = label
        def rename(self, dst, src): pass # nothing to do
        def __repr__(self):
            return 'TACGoto(%s)'%(self.label,)
    class TACIf(TACStatement):
        def __init__(self, cond, count):
            self.cond = cond
            self.count = count # number of following statements to only run if cond is true
        def rename(self, dst, src):
            if self.cond == dst:
                self.cond = src
        def __repr__(self):
            return 'TACIf(%r, %d)'%(self.cond,self.count)
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
    class Genbool(Gensym):
        def __repr__(self):
            return '?(%d)'%(self.n,)
    def gensym(self):
        n = self.gennum
        self.gennum += 1
        return self.Gensym(n)
    def genbool(self):
        n = self.gennum
        self.gennum += 1
        return self.Genbool(n)
    def __init__(self):
        self.scopes = [{}]
        self.functions = {None:[]}
        self.in_func = None
        self.strings = {}
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
                    return (self.Identifier(typ, lval.name), [], [])
            raise TACError("Name", lval.name, "not in scope")
        if isinstance(lval, PAR.Dereference):
            pointee, pre = self.get_rvalue(lval.erand)
            if not isinstance(pointee.typ, PAR.Pointer):
                raise TACError("Dereferencing non-pointer", lval.erand)
            sym = self.gensym()
            typ = pointee.typ.pointee
            self.scopes[-1][sym] = (LEX.Auto('auto'), typ)
            pre.insert(0, self.TACDeclare(sym, LEX.Auto('auto'), typ))
            post = [self.TACWrite(pointee.name, sym)]
            return (self.Identifier(typ, sym), pre, post)
        raise NotImplementedError(lval)
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
        if isinstance(rval, PAR.Literal):
            typ = PAR.ValueOfType('byte')
            return (self.Identifier(typ, rval.value), [])
        if isinstance(rval, PAR.LongLiteral):
            typ = PAR.ValueOfType('word')
            return (self.Identifier(typ, rval.value), [])
        if isinstance(rval, PAR.StringLiteral):
            sym = self.gensym()
            typ = PAR.Pointer(PAR.ValueOfType('byte'))
            self.scopes[-1][sym] = (LEX.Auto('auto'), typ)
            stmts = [self.TACDeclare(sym, LEX.Auto('auto'), typ)]
            string = self.gensym()
            self.strings[string] = rval.value
            styp = PAR.Array(PAR.ValueOfType('byte'), len(rval.value) + 1)
            stmts.append(self.TACDeclare(string, LEX.Static('static'), styp))
            stmts.append(self.TACAssign(sym, string))
            return (self.Identifier(typ, sym), stmts)
        raise NotImplementedError(rval)
    def emit_assignish(self, op, lvalue, rvalue):
        if not isinstance(lvalue, self.Identifier):
            raise TACError("Uninterpreted lvalue", lvalue)
        if not isinstance(rvalue, self.Identifier):
            raise TACError("Uninterpreted rvalue", rvalue)
        if isinstance(lvalue.typ, PAR.Pointer) and isinstance(op, (LEX.Add, LEX.Subtract)):
            if rvalue.typ not in (PAR.ValueOfType('byte'), PAR.ValueOfType('word')):
                raise TACError("Type mismatch in assignment", lvalue, op, rvalue)
        elif lvalue.typ != rvalue.typ:
            raise TACError("Type mismatch in assignment", lvalue, op, rvalue)
        if isinstance(op, LEX.Add):
            return [self.TACAdd(lvalue.name, rvalue.name)]
        if isinstance(op, LEX.Assignment):
            return [self.TACAssign(lvalue.name, rvalue.name)]
        raise NotImplementedError(op)
    def emit_return(self, rvalue):
        if self.in_func is None:
            raise TACError("return outside function")
        decl = self.in_func[1]
        typ = decl.bound
        if isinstance(rvalue, self.Identifier):
            if typ != rvalue.typ:
                raise TACError("Type mismatch returning", rvalue, "from", decl)
            return [self.TACReturn(rvalue.name)]
        if isinstance(rvalue, self.Genbool):
            sym = self.gensym()
            styp = PAR.ValueOfType('bool')
            if typ != styp:
                raise TACError("Type mismatch returning", rvalue, "from", decl)
            self.scopes[-1][sym] = (LEX.Auto('auto'), styp)
            return [self.TACDeclare(sym, LEX.Auto('auto'), styp),
                    self.TACRename(sym, rvalue),
                    self.TACReturn(sym)]
        raise TACError("Uninterpreted rvalue", rvalue)
    def walk_expr(self, expr): # this always returns an rvalue
        if isinstance(expr, PAR.IdentifierExpression):
            return self.get_rvalue(expr)
        if isinstance(expr, PAR.AssignIsh):
            lval = expr.left
            rval = expr.right
            lvalue, pre, post = self.get_lvalue(lval)
            rvalue, rs = self.get_rvalue(rval)
            return (lvalue, rs + pre + self.emit_assignish(expr.op, lvalue, rvalue) + post) # lvalue becomes an rvalue, returns the value written
        if isinstance(expr, PAR.Comparison):
            left, ls = self.get_rvalue(expr.left)
            right, rs = self.get_rvalue(expr.right)
            sym = self.genbool() # either use in a conditional context, or assign (really Rename) to a variable
            # note that we don't TACDeclare sym, nor add it to the scope
            return (sym, ls + rs + [self.TACCompare(expr.op, left, right)])
        if isinstance(expr, PAR.Postcrement):
            if isinstance(expr.op, LEX.Incr):
                crement = 1
            elif isinstance(expr.op, LEX.Dccr):
                crement = -1
            else: # can't happen
                raise TACError("Weird excrement op", expr) # well, what would _you_ call the set {increment, decrement}?
            lvalue, pre, post = self.get_lvalue(expr.erand)
            sym = self.gensym()
            typ = lvalue.typ
            self.scopes[-1][sym] = (LEX.Auto('auto'), typ)
            return (sym, [self.TACDeclare(sym, LEX.Auto('auto'), typ)] + pre +
                         [self.TACAssign(sym, lvalue), self.TACAdd(lvalue, crement)] + post)
        if isinstance(expr, PAR.Precrement):
            if isinstance(expr.op, LEX.Incr):
                crement = 1
            elif isinstance(expr.op, LEX.Dccr):
                crement = -1
            else: # can't happen
                raise TACError("Weird excrement op", expr)
            lvalue, pre, post = self.get_lvalue(expr.erand)
            return (lvalue, pre + [self.TACAdd(lvalue, crement)] + post)
        if isinstance(expr, PAR.FunctionCall):
            func, fs = self.get_rvalue(expr.func)
            if not isinstance(func.typ, PAR.FunctionDecl):
                raise TACError("Calling non-function", expr, "is", func)
            rtyp = func.typ.bound
            atyp = func.typ.arglist
            args = []
            types = []
            for a in expr.args.args:
                arg = self.get_rvalue(a)
                args.append(arg)
                types.append((None, arg[0].typ))
            if atyp != PAR.ArgList(types):
                self.err(atyp)
                self.err(PAR.ArgList(types))
                raise TACError("Parameter types don't match in call", expr)
            sym = self.gensym()
            self.scopes[-1][sym] = (LEX.Auto('auto'), rtyp)
            return (sym, [self.TACDeclare(sym, LEX.Auto('auto'), rtyp)] + fs +
                         [self.TACCall(func, sym, args)])
        if isinstance(expr, PAR.Literal):
            typ = PAR.ValueOfType('byte')
            return (self.Identifier(typ, expr.value), [])
        raise NotImplementedError(expr)
    def walk_stmt(self, stmt):
        if isinstance(stmt, PAR.ExpressionStatement):
            _, stmts = self.walk_expr(stmt.expr)
            return stmts
        elif isinstance(stmt, PAR.ReturnStatement):
            rvalue, stmts = self.walk_expr(stmt.expr)
            return stmts + self.emit_return(rvalue)
        elif isinstance(stmt, PAR.Label):
            return [self.TACLabel(stmt.name)]
        elif isinstance(stmt, PAR.IfStatement):
            cond, stmts = self.walk_expr(stmt.cond)
            then = self.walk_stmt(stmt.then)
            return stmts + [self.TACIf(cond, len(then))] + then
        elif isinstance(stmt, PAR.GotoStatement):
            return [self.TACGoto(stmt.label)]
        else:
            raise NotImplementedError(stmt)
    def declare(self, declaration):
        stmts = []
        name, sc, decl, init = declaration
        if name in self.scopes[-1]:
            raise TACError("Identifier", name, "redefined in same scope")
        if sc is None:
            if isinstance(decl, PAR.FunctionDecl):
                sc = LEX.Extern("extern")
            else:
                sc = LEX.Auto("auto")
        self.scopes[-1][name] = (sc, decl)
        if isinstance(sc, LEX.Auto):
            if init is None:
                stmts.append(self.TACDeclare(name, sc, decl))
            else:
                rvalue, rs = self.get_rvalue(init)
                stmts.extend(rs)
                if not isinstance(rvalue, self.Identifier):
                    raise TACError("Uninterpreted rvalue", rvalue)
                if isinstance(rvalue.name, self.Gensym):
                    stmts.append(self.TACRename(name, rvalue.name))
                else:
                    stmts.insert(0, self.TACDeclare(name, sc, decl))
                    stmts.append(self.TACAssign(name, rvalue))
        elif isinstance(sc, LEX.Extern):
            if init is not None:
                raise TACError("extern variable", name, "has initialiser", init)
            stmts.append(self.TACDeclare(name, sc, decl))
        else:
            raise NotImplementedError(sc)
        return stmts
    def walk(self, block):
        func = []
        for declaration in block.local:
            try:
                func.extend(self.declare(declaration))
            except:
                self.err("In declaration %r"%(declaration,))
                raise
        for stmt in block.body:
            try:
                func.extend(self.walk_stmt(stmt))
            except:
                self.err("In stmt %r"%(stmt,))
                raise
        return func
    def normalise(self, func):
        # apply any Renames
        declares = [t for t in func if isinstance(t, self.TACDeclare)]
        renames = [t for t in func if isinstance(t, self.TACRename)]
        the_rest = [t for t in func if not isinstance(t, (self.TACDeclare, self.TACRename))]
        for rename in renames:
            if not isinstance(rename.src, self.Genbool):
                for declare in declares:
                    if declare.name == rename.src:
                        declare.name = rename.dst
                        break
                else:
                    raise TACError("Found no TACDeclare matching", rename)
            for t in the_rest:
                t.rename(rename.src, rename.dst)
        return [t for t in func if not isinstance(t, self.TACRename)]
    def evaluate_constant(self, expr):
        if isinstance(expr, (PAR.Literal, PAR.LongLiteral)):
            return expr.value
        raise NotImplementedError(expr)
    def add(self, name, sc, decl, init):
        code = self.functions[self.in_func]
        if isinstance(decl, PAR.FunctionDecl):
            if isinstance(init, PAR.BlockStatement):
                if isinstance(sc, LEX.Extern):
                    raise TACError("extern function with definition")
                if self.in_func is not None: # should be impossible, parser won't allow it
                    raise TACError("Nested function definition")
                self.in_func = (name, decl)
                self.scopes.append(self.arg_list(decl.arglist))
                try:
                    func = self.walk(init)
                except:
                    self.err("In: %s %r"%(name, decl))
                    self.err(pprint.pformat(init))
                    raise
                self.scopes.pop(-1)
                self.in_func = None
                self.functions[name] = self.normalise(func)
                self.scopes[-1][name] = (sc, decl)
            else: # function declaration without definition
                if not isinstance(sc, LEX.Extern):
                    if sc:
                        raise TACError("function prototype is", sc)
                    sc = LEX.Extern("extern")
                self.scopes[-1][name] = (sc, decl)
        elif isinstance(decl, (PAR.ValueOfType, PAR.Pointer)):
            if not isinstance(sc, LEX.Extern):
                if sc is None:
                    sc = LEX.Auto("auto")
                code.append(self.TACDeclare(name, sc, decl))
                if init is not None:
                    value = self.evaluate_constant(init)
                    code.append(self.TACInitGlobal(name, value))
            self.scopes[-1][name] = (sc, decl)
        else:
            raise NotImplementedError(decl, init)
    def err(self, text):
        print >>sys.stderr, text

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

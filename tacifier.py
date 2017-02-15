#!/usr/bin/python

import sys, pprint
import ast_build as AST

## Convert parse tree to Two-Address Code intermediate form

class TACError(Exception): pass
class UnhandledEntity(TACError):
    "I haven't implemented it yet"
    def __init__(self, entity):
        self.entity = entity
    def __str__(self):
        return '%s %s' % (type(self.entity), self.entity)

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
            return 'TACDeclare(%s, %s, %s)'%(self.name, self.sc, self.typ)
    class TACStructDef(TACStatement):
        def __init__(self, tag, defn):
            self.tag = tag
            self.defn = defn
        def rename(self, dst, src):
            raise TACError("Tried to rename(%s, %s, %s)"%(self, dst, src))
        def __repr__(self):
            return 'TACStructDef(%s, %s)'%(self.tag, self.defn)
    class TACInitGlobal(TACStatement):
        def __init__(self, name, value):
            self.name = name
            self.value = value
        def rename(self, dst, src):
            raise NotImplementedError()
        def __repr__(self):
            return 'TACInitGlobal(%s, %s)'%(self.name, self.value)
    class TACRename(TACStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def rename(self, dst, src):
            # I don't know if this should be allowed.  But hopefully not.
            raise TACError("Tried to rename(%s, %s, %s)"%(self, dst, src))
        def __repr__(self):
            return 'TACRename(%s, %s)'%(self.dst, self.src)
    class TACKill(TACStatement):
        def __init__(self, name):
            self.name = name
        def rename(self, dst, src):
            if self.name == dst:
                raise TACError("Tried to rename", self, "to", src)
        def __repr__(self):
            return 'TACKill(%s)'%(self.name,)
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
            return 'TACDeref(%s, %s)'%(self.dst, self.src)
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
            return 'TACWrite(%s, %s)'%(self.dst, self.src)
    class TACMemberRead(TACStatement): # read through a struct pointer
        def __init__(self, dst, tag, src):
            self.dst = dst
            self.tag = tag
            self.src = src
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.src == dst:
                self.src = src
        def __repr__(self):
            return 'TACMemberRead(%s, %s, %s)'%(self.dst, self.tag, self.src)
    class TACMemberWrite(TACStatement): # write through a struct pointer
        def __init__(self, dst, tag, src):
            self.dst = dst
            self.tag = tag
            self.src = src
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.src == dst:
                self.src = src
        def __repr__(self):
            return 'TACMemberWrite(%s, %s, %s)'%(self.dst, self.tag, self.src)
    class TACAssign(TACStatement):
        def __init__(self, dst, src, kills=False):
            self.dst = dst
            self.src = src
            self.kills = kills
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.src == dst:
                self.src = src
        def __repr__(self):
            k = ''
            if self.kills: k = ' (kill)'
            return 'TACAssign(%s, %s%s)'%(self.dst, self.src, k)
    class TACAddress(TACStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.src == dst:
                self.src = src
        def __repr__(self):
            return 'TACAddress(%s, %s)'%(self.dst, self.src)
    class TACCompare(TACStatement):
        def __init__(self, dst, op, left, right):
            self.dst = dst
            self.op = op
            self.left = left
            self.right = right
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.left == dst:
                self.left = src
            if self.right == dst:
                self.right = src
        def __repr__(self):
            return 'TACCompare(%s, %s, %s, %s)'%(self.dst, self.op, self.left, self.right)
    class TACAdd(TACStatement):
        def __init__(self, dst, src, kills=False):
            self.dst = dst
            self.src = src
            self.kills = kills
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.src == dst:
                self.src = src
        def __repr__(self):
            k = ''
            if self.kills: k = ' (kill)'
            return 'TACAdd(%s, %s%s)'%(self.dst, self.src, k)
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
            for arg in self.args:
                if arg == dst:
                    arg = src
        def __repr__(self):
            return 'TACCall(%s, %s, %s)'%(self.func, self.ret, self.args)
    class TACReturn(TACStatement):
        def __init__(self, src, kills=False):
            self.src = src
            self.kills = kills
        def rename(self, dst, src):
            if self.src == dst:
                self.src = src
        def __repr__(self):
            k = ''
            if self.kills: k = ' (kill)'
            return 'TACReturn(%s%s)'%(self.src, k)
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
        def __init__(self, cond, label):
            self.cond = cond
            self.label = label
        def rename(self, dst, src):
            if self.cond == dst:
                self.cond = src
        def __repr__(self):
            return 'TACIf(%s, %s)'%(self.cond, self.label)
    class Value(object):
        def __init__(self, typ):
            self.typ = typ
        def __repr__(self):
            return 'Value(%s)'%(self.typ,)
    class Identifier(Value):
        def __init__(self, typ, name):
            super(TACifier.Identifier, self).__init__(typ)
            self.name = name
        def rename(self, dst, src):
            if self.name == dst:
                self.name = src
        def __repr__(self):
            return 'Identifier(%s, %s)'%(self.typ, self.name)
    class FlagIdent(Identifier):
        def __init__(self, flag):
            super(TACifier.FlagIdent, self).__init__(AST.Bool(), flag)
        def rename(self, dst, src):
            if self.name == dst:
                raise TACError("Tried to rename", self, "to", src)
        def __repr__(self):
            return 'FlagIdent(%s)' % (self.name,)
    class Gensym(object):
        def __init__(self, n):
            self.n = n
        def __repr__(self):
            return '$(%d)'%(self.n,)
    def gensym(self):
        n = self.gennum
        self.gennum += 1
        return self.Gensym(n)
    def genlabel(self):
        n = self.gennum
        self.gennum += 1
        return '_genlabel_%d'%(n,)
    def __init__(self):
        self.scopes = [{}]
        self.functions = {None:[]}
        self.in_func = None
        self.strings = {}
        self.gennum = 0
        self.structs = {}
    def arg_list(self, arglist):
        scope = {}
        for arg in arglist:
            if arg.ident in scope:
                raise TACError("Name", name, "redeclared within parameter list")
            scope[arg.ident] = (AST.Auto, arg.typ)
        return scope
    def get_member_type(self, styp, member):
        if not isinstance(styp, AST.Struct):
            raise TACError("Tried to get member of non-struct", styp)
        if not self.structs.get(styp.tag):
            raise TACError("Tried to get member of incomplete struct", styp.tag)
        sdef = self.structs[styp.tag].defn
        for decl in sdef:
            if decl.name == member:
                return decl.typ
        raise TACError("Tried to get non-existent member", member, "of struct", styp.tag)
    def get_lvalue(self, lval):
        if isinstance(lval, AST.Identifier):
            for scope in reversed(self.scopes):
                if lval.ident in scope:
                    sc, typ = scope[lval.ident]
                    return (self.Identifier(typ, lval.ident), [], [])
            raise TACError("Name", lval.ident, "not in scope")
        if isinstance(lval, AST.UnaryExpr):
            if lval.op == '*':
                pointee, pre = self.walk_expr(lval.arg)
                if not isinstance(pointee.typ, AST.Pointer):
                    raise TACError("Dereferencing non-pointer", lval.arg)
                sym = self.gensym()
                typ = pointee.typ.target
                self.scopes[-1][sym] = (AST.Auto, typ)
                pre.insert(0, self.TACDeclare(sym, AST.Auto, typ))
                post = [self.TACWrite(pointee.name, sym)]
                if isinstance(pointee.name, self.Gensym): # no-one but us has a reference to it
                    post.append(self.TACKill(pointee.name))
                    del self.scopes[-1][pointee.name]
                return (self.Identifier(typ, sym), pre, post)
            raise NotImplementedError(lval)
        if isinstance(lval, AST.MemberExpr):
            target, pre = self.walk_expr(lval.target)
            member = lval.tag
            if lval.op == '->':
                if not isinstance(target.typ, AST.Pointer):
                    raise TACError("Dereferencing (by ->) non-pointer", lval.target)
                sym = self.gensym()
                typ = self.get_member_type(target.typ.target, member)
                self.scopes[-1][sym] = (AST.Auto, typ)
                pre.insert(0, self.TACDeclare(sym, AST.Auto, typ))
                post = [self.TACMemberWrite(target.name, member, sym)]
                if isinstance(target.name, self.Gensym): # no-one but us has a reference to it
                    post.append(self.TACKill(target.name))
                    del self.scopes[-1][target.name]
                return (self.Identifier(typ, sym), pre, post)
            raise NotImplementedError(lval)
        raise NotImplementedError(lval)
    def get_rvalue(self, rval):
        # TODO check if returning an Array; if so, decay it to a pointer by taking its address
        if isinstance(rval, AST.Identifier):
            for scope in reversed(self.scopes):
                if rval.ident in scope:
                    sc, typ = scope[rval.ident]
                    return (self.Identifier(typ, rval.ident), [])
            raise TACError("Name", rval.ident, "not in scope")
        if isinstance(rval, AST.IntConst):
            typ = AST.Word() if rval.long else AST.Byte()
            return (self.Identifier(typ, rval), [])
        if isinstance(rval, AST.FlagIdent):
            return (self.FlagIdent(rval.flag), [])
        if isinstance(rval, AST.StringLiteral):
            sym = self.gensym()
            typ = AST.Pointer.make(AST.Byte(), 'const')
            self.scopes[-1][sym] = (AST.Auto, typ)
            stmts = [self.TACDeclare(sym, AST.Auto, typ)]
            string = self.gensym()
            self.strings[string] = rval.text
            styp = AST.Array.make(AST.Byte(), len(rval.text) + 1)
            stmts.append(self.TACDeclare(string, AST.Static, styp))
            stmts.append(self.TACAddress(sym, string))
            return (self.Identifier(typ, sym), stmts)
        raise UnhandledEntity(rval)
    def emit_assignish(self, op, lvalue, rvalue, killr=False):
        if not isinstance(lvalue, self.Identifier):
            raise TACError("Uninterpreted lvalue", lvalue)
        if not isinstance(rvalue, self.Identifier):
            raise TACError("Uninterpreted rvalue", rvalue)
        if isinstance(rvalue.typ, AST.Array): # 'decay' to a pointer
            raise UnhandledEntity(rvalue) # TODO qualifiers?
            rvalue.typ = AST.Pointer(rvalue.typ.typ)
            killr = False
        if isinstance(lvalue.typ, AST.Pointer) and op != '=':
            if not AST.Word.compat(rvalue.typ):
                raise TACError("Type mismatch in assignment", lvalue, op, rvalue)
        elif not lvalue.typ.compat(rvalue.typ):
            raise TACError("Type mismatch in assignment", lvalue, op, rvalue)
        if op == '+=':
            return [self.TACAdd(lvalue.name, rvalue.name, kills=killr)]
        if op == '=':
            return [self.TACAssign(lvalue.name, rvalue.name, kills=killr)]
        raise NotImplementedError(op)
    def emit_return(self, rvalue, killr=False):
        if self.in_func is None:
            raise TACError("return outside function")
        decl = self.in_func[1]
        typ = decl.ret
        if isinstance(rvalue, self.Identifier):
            if not typ.compat(rvalue.typ):
                raise TACError("Type mismatch returning", rvalue, "from", decl)
            return [self.TACReturn(rvalue.name, kills=killr)]
        raise TACError("Uninterpreted rvalue", rvalue)
    def walk_expr(self, expr): # this always returns an rvalue
        if isinstance(expr, (AST.IntConst, AST.EnumConst, AST.StringLiteral, AST.Identifier, AST.FlagIdent)):
            return self.get_rvalue(expr)
        if isinstance(expr, AST.AssignExpr):
            lval = expr.left
            rval = expr.right
            lvalue, pre, post = self.get_lvalue(lval)
            rvalue, rs = self.walk_expr(rval)
            killr = isinstance(rvalue.name, self.Gensym) # no-one but us has a reference to it
            return (lvalue, rs + pre + self.emit_assignish(expr.op, lvalue, rvalue, killr) + post) # lvalue becomes an rvalue, returns the value written
        if isinstance(expr, AST.EqualityExpr):
            left, ls = self.walk_expr(expr.left)
            right, rs = self.walk_expr(expr.right)
            sym = self.gensym() # either use in a conditional context, or assign (really Rename) to a variable
            typ = AST.Bool()
            return (self.Identifier(typ, sym), ls + rs + [self.TACDeclare(sym, AST.Auto, typ),
                                                          self.TACCompare(sym, expr.op, left.name, right.name)])
        if isinstance(expr, AST.UnaryExpr):
            if expr.op == '*':
                pointee, ps = self.walk_expr(expr.arg)
                if not isinstance(pointee.typ, AST.Pointer):
                    raise TACError("Dereferencing non-pointer", expr.arg)
                sym = self.gensym()
                typ = pointee.typ.target
                self.scopes[-1][sym] = (AST.Auto, typ)
                stmts = ps
                stmts.append(self.TACDeclare(sym, AST.Auto, typ))
                stmts.append(self.TACDeref(sym, pointee.name))
                if isinstance(pointee.name, self.Gensym): # no-one but us has a reference to it
                    stmts.append(self.TACKill(pointee.name))
                    del self.scopes[-1][pointee.name]
                return (self.Identifier(typ, sym), stmts)
            raise UnhandledEntity(expr)
        if isinstance(expr, AST.PostcremExpr):
            if expr.op == '++':
                crement = 1
            elif expr.op == '--':
                crement = -1
            else: # can't happen
                raise TACError("Weird excrement op", expr) # well, what would _you_ call the set {increment, decrement}?
            lvalue, pre, post = self.get_lvalue(expr.target)
            typ = lvalue.typ
            if AST.Word().compat(typ):
                crement = typ.make(crement)
            elif isinstance(typ, AST.Pointer):
                crement = AST.Word().make(crement)
            else:
                raise TACError("Can't postcrement type", typ)
            return (lvalue, pre + [self.TACAdd(lvalue.name, crement)] + post)
        if isinstance(expr, AST.PrecremExpr):
            if expr.op == '++':
                crement = 1
            elif expr.op == '--':
                crement = -1
            else: # can't happen
                raise TACError("Weird excrement op", expr)
            lvalue, pre, post = self.get_lvalue(expr.arg)
            typ = lvalue.typ
            typ = lvalue.typ
            if AST.Word().compat(typ):
                crement = typ.make(crement)
            elif isinstance(typ, AST.Pointer):
                crement = AST.Word().make(crement)
            else:
                raise TACError("Can't precrement type", typ)
            return (lvalue, pre + [self.TACAdd(lvalue.name, crement)] + post)
        if isinstance(expr, AST.MemberExpr):
            target, pre = self.walk_expr(expr.target)
            member = expr.tag
            if expr.op == '->':
                if not isinstance(target.typ, AST.Pointer):
                    raise TACError("Dereferencing (by ->) non-pointer", expr.target)
                sym = self.gensym()
                typ = self.get_member_type(target.typ.target, member)
                self.scopes[-1][sym] = (AST.Auto, typ)
                pre.insert(0, self.TACDeclare(sym, AST.Auto, typ))
                pre.append(self.TACMemberRead(target.name, member, sym))
                if isinstance(target.name, self.Gensym): # no-one but us has a reference to it
                    pre.append(self.TACKill(target.name))
                    del self.scopes[-1][target.name]
                return (self.Identifier(typ, sym), pre)
            raise NotImplementedError(lval)
        raise UnhandledEntity(expr)
        if isinstance(expr, PAR.Comparison):
            left, ls = self.walk_expr(expr.left)
            right, rs = self.walk_expr(expr.right)
            sym = self.gensym() # either use in a conditional context, or assign (really Rename) to a variable
            typ = PAR.ValueOfType('bool')
            return (self.Identifier(typ, sym), ls + rs + [self.TACDeclare(sym, LEX.Auto('auto'), typ),
                                                          self.TACCompare(sym, expr.op, left.name, right.name)])
        if isinstance(expr, PAR.FunctionCall):
            func, fs = self.walk_expr(expr.func)
            if not isinstance(func.typ, PAR.FunctionDecl):
                raise TACError("Calling non-function", expr, "is", func)
            rtyp = func.typ.bound
            atyp = func.typ.arglist
            args = []
            stmts = []
            types = []
            for a in expr.args.args:
                arg, st = self.walk_expr(a)
                args.append(arg)
                stmts.extend(st)
                types.append((None, arg.typ))
            if atyp != PAR.ArgList(types):
                self.err(atyp)
                self.err(PAR.ArgList(types))
                raise TACError("Parameter types don't match in call", expr)
            if rtyp == PAR.ValueOfType('void'):
                return (None, fs + stmts + [self.TACCall(func, None, args)])
            sym = self.gensym()
            self.scopes[-1][sym] = (LEX.Auto('auto'), rtyp)
            return (self.Identifier(rtyp, sym), [self.TACDeclare(sym, LEX.Auto('auto'), rtyp)] + fs + stmts +
                                                [self.TACCall(func, sym, args)])
        raise NotImplementedError(expr)
    def walk_stmt(self, stmt):
        if isinstance(stmt, AST.ExpressionStatement):
            rvalue, stmts = self.walk_expr(stmt.expr)
            if rvalue is not None:
                if isinstance(rvalue.name, self.Gensym): # no-one else has a reference to it
                    stmts.append(self.TACKill(rvalue.name))
                    del self.scopes[-1][rvalue.name]
            return stmts
        elif isinstance(stmt, AST.ReturnStatement):
            rvalue, stmts = self.walk_expr(stmt.value)
            killr = rvalue is not None and isinstance(rvalue.name, self.Gensym) # no-one else has a reference to it
            return stmts + self.emit_return(rvalue, killr=killr)
        elif isinstance(stmt, AST.LabelStatement):
            return [self.TACLabel(stmt.label)]
        elif isinstance(stmt, AST.IfStatement):
            cond, stmts = self.walk_expr(stmt.condition)
            then = self.walk_stmt(stmt.true)
            if stmt.false:
                raise UnhandledEntity(stmt)
            label = self.genlabel()
            return stmts + [self.TACIf(cond, label)] + then + [self.TACLabel(label)]
        elif isinstance(stmt, AST.GotoStatement):
            return [self.TACGoto(stmt.label)]
        else:
            raise NotImplementedError(stmt)
    def declare(self, declaration):
        stmts = []
        name = declaration.decl_spec.ident
        sc = declaration.sc
        decl = declaration.decl_spec.object
        init = declaration.init
        if name in self.scopes[-1]:
            raise TACError("Identifier", name, "redefined in same scope")
        if sc is None:
            if isinstance(decl, AST.Function):
                sc = AST.Extern
            else:
                sc = AST.Auto
        self.scopes[-1][name] = (sc, decl.typ)
        if init is None:
            stmts.append(self.TACDeclare(name, sc, decl.typ))
        elif sc.extern:
            raise TACError("extern variable", name, "has initialiser", init)
        else:
            rvalue, rs = self.walk_expr(init)
            if not decl.typ.compat(rvalue.typ):
                self.err("Want: %s"%(decl.typ,))
                self.err("Have: %s"%(rvalue.typ,))
                raise TACError("Initialiser for %s has wrong type"%(name,))
            stmts.extend(rs)
            if not isinstance(rvalue, self.Identifier):
                raise TACError("Uninterpreted rvalue", rvalue)
            if isinstance(rvalue.name, self.Gensym):
                stmts.append(self.TACRename(name, rvalue.name))
            else:
                stmts.insert(0, self.TACDeclare(name, sc, decl))
                stmts.append(self.TACAssign(name, rvalue.name))
        return stmts
    def walk(self, block):
        func = []
        for declaration in block.decls:
            typ = declaration.typ
            if isinstance(typ, AST.Struct):
                func.extend(self.declare_struct(typ.tag, typ.body))
            try:
                for d in declaration.declarations:
                    func.extend(self.declare(d))
            except:
                self.err("In declaration %s"%(declaration,))
                raise
        for stmt in block.stmts:
            try:
                func.extend(self.walk_stmt(stmt))
            except:
                self.err("In stmt %s"%(stmt,))
                raise
        return func
    def normalise(self, func):
        # apply any Renames
        declares = [t for t in func if isinstance(t, self.TACDeclare)]
        renames = [t for t in func if isinstance(t, self.TACRename)]
        the_rest = [t for t in func if not isinstance(t, (self.TACDeclare, self.TACRename))]
        for rename in renames:
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
            return expr
        raise NotImplementedError(expr)
    def declare_struct(self, tag, body):
        if body is None:
            self.structs.setdefault(tag, None)
            return []
        elif self.structs.get(tag) is None:
            struct = []
            self.scopes.append({})
            for declaration in body:
                typ = declaration.typ
                if isinstance(typ, AST.Struct):
                    struct.extend(self.declare_struct(typ.tag, typ.body))
                try:
                    for d in declaration.declarations:
                        struct.extend(self.declare(d))
                except:
                    self.err("In declaration %s"%(declaration,))
                    raise
            self.scopes.pop(-1)
            self.structs[tag] = self.TACStructDef(tag, struct)
            return [self.structs[tag]]
        else:
            raise TACError("struct %s redefined"%(tag,))
    def add(self, decl):
        code = self.functions[self.in_func]
        if isinstance(decl, AST.Declare):
            if isinstance(decl.typ, AST.Struct):
                body = decl.typ.body
                tag = decl.typ.tag
                code.extend(self.declare_struct(tag, body))
            for d in decl.declarations:
                code.extend(self.declare(d))
            return
        if isinstance(decl, AST.FunctionDefn):
            sc = decl.sc
            if sc is None:
                sc = AST.Auto
            if sc.extern:
                raise TACError("extern function with definition")
            if self.in_func is not None: # should be impossible, parser won't allow it
                raise TACError("Nested function definition")
            d = decl.decl_spec
            typ = d.object.typ
            self.in_func = (d.ident, typ)
            self.scopes.append(self.arg_list(typ.params))
            try:
                func = self.walk(decl.body)
            except:
                self.err("In: %s %s" % self.in_func)
                self.err(str(decl.body))
                raise
            self.scopes.pop(-1)
            self.in_func = None
            self.functions[d.ident] = self.normalise(func)
            self.scopes[-1][d.ident] = (sc, typ)
            return
        raise TACError("Bad top-level decl", type(decl), str(decl))
    def err(self, text):
        print >>sys.stderr, text

## Entry point
def tacify(ast):
    tac = TACifier()
    for decl in ast.decls:
        tac.add(decl)
    return tac

## Test code

if __name__ == "__main__":
    import parser
    if len(sys.argv) > 1:
        with open(sys.argv[1], 'r') as f:
            source = f.read()
    else:
        source = sys.stdin.read()
    parse_tree = parser.parse(source)
    ast = AST.AST_builder(parse_tree)
    for decl in ast.decls:
        print decl
    print
    tac = TACifier()
    for decl in ast.decls:
        tac.add(decl)
    print "TAC scopes:"
    for i,scope in enumerate(tac.scopes):
        print i
        for name, (sc, typ) in scope.iteritems():
            print '\t%s %s %s' % (sc, name, typ)
    print "TAC functions:"
    pprint.pprint(tac.functions)
    print "TAC strings:"
    pprint.pprint(tac.strings)
    print "TAC structs:"
    pprint.pprint(tac.structs)
    assert tac.in_func is None, tac.in_func
    assert len(tac.scopes) == 1

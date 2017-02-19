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
    PREFER_RETURN = '^R' # Prefer register for returning this type
    PREFER_LOWBYTE = '^L' # Prefer low byte of a splittable register
    PREFER_ADDRESS = '^A' # Will be used as an address; prefer HL
    class TACStatement(object):
        def __init__(self, dst, src, prefer=''):
            self.dst = dst
            self.src = src
            # What kind of register would we like the dst in?
            self.prefer = prefer
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.src == dst:
                self.src = src
        def __repr__(self):
            return '%s(%s%s, %s)'%(self.__class__.__name__, self.dst, self.prefer, self.src)
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
            if self.tag == dst:
                raise TACError("Tried to rename(%s, %s, %s)"%(self, dst, src))
        def __repr__(self):
            return 'TACStructDef(%s, %s)'%(self.tag, self.defn)
    class TACEnumDef(TACStatement):
        def __init__(self, tag, typ, defn):
            self.tag = tag
            self.typ = typ
            self.defn = defn
        def rename(self, dst, src):
            if self.tag == dst:
                raise TACError("Tried to rename(%s, %s, %s)"%(self, dst, src))
        def __repr__(self):
            return 'TACEnumDef(%s, %s, %s)'%(self.tag, self.typ, self.defn)
    class TACRename(TACStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def rename(self, dst, src):
            # I don't know if this should be allowed.  But hopefully not.
            raise TACError("Tried to rename(%s, %s, %s)"%(self, dst, src))
        def __repr__(self):
            return 'TACRename(%s, %s)'%(self.dst, self.src)
    class TACDeref(TACStatement): # read through a pointer
        pass
    class TACWrite(TACStatement): # write through a pointer.  Implies kill of dst as well as src
        pass
    class TACMemberRead(TACStatement): # read through a struct pointer
        def __init__(self, dst, src, tag, prefer=''):
            self.dst = dst
            self.src = src
            self.tag = tag
            self.prefer = prefer
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.src == dst:
                self.src = src
        def __repr__(self):
            return 'TACMemberRead(%s%s, %s, %s)'%(self.dst, self.prefer, self.src, self.tag)
    class TACMemberWrite(TACStatement): # write through a struct pointer.  Implies kill of dst as well as src
        def __init__(self, dst, tag, src, prefer=''):
            self.dst = dst
            self.tag = tag
            self.src = src
            self.prefer = prefer
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.src == dst:
                self.src = src
        def __repr__(self):
            return 'TACMemberWrite(%s%s, %s, %s)'%(self.dst, self.prefer, self.tag, self.src)
    class TACAssign(TACStatement):
        pass
    class TACAddress(TACStatement):
        def __init__(self, dst, src, prefer=''):
            self.dst = dst
            self.src = src
            self.prefer = prefer
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.src == dst:
                self.src = src
        def __repr__(self):
            return 'TACAddress(%s%s, %s)'%(self.dst, self.prefer, self.src)
    class TACCompare(TACStatement): # implies kill of left and right
        def __init__(self, dst, op, left, right, prefer=''):
            self.dst = dst
            self.op = op
            self.left = left
            self.right = right
            self.prefer = prefer
        def rename(self, dst, src):
            if self.dst == dst:
                self.dst = src
            if self.left == dst:
                self.left = src
            if self.right == dst:
                self.right = src
        def __repr__(self):
            return 'TACCompare(%s%s, %s, %s, %s)'%(self.dst, self.prefer, self.op, self.left, self.right)
    class TACAdd(TACStatement):
        pass
    class TACCall(TACStatement): # implies kill of args
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
        def __init__(self, src):
            self.src = src
        def rename(self, dst, src):
            if self.src == dst:
                self.src = src
        def __repr__(self):
            return 'TACReturn(%s)'%(self.src,)
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
    class TACCondGoto(TACStatement): # an inverted TACIf
        def __init__(self, cond, label):
            self.cond = cond
            self.label = label
        def rename(self, dst, src):
            if self.cond == dst:
                self.cond = src
        def __repr__(self):
            return 'TACCondGoto(%s, %s)'%(self.cond, self.label)
    class TACInit(TACStatement):
        pass
    class Value(object):
        def __init__(self, typ):
            self.typ = typ
        def __repr__(self):
            return 'Value(%s)'%(self.typ,)
    class Member(Value): # used for initialiser designators
        def __init__(self, typ, struct, tag):
            super(TACifier.Member, self).__init__(typ)
            self.struct = struct
            self.tag = tag
        def rename(self, dst, src):
            self.struct.rename(dst, src)
        def __repr__(self):
            return 'Member(%s, %s, %s)'%(self.typ, self.struct, self.tag)
    class Element(Value): # used for initialiser designators
        def __init__(self, typ, array, subscript):
            super(TACifier.Element, self).__init__(typ)
            self.array = array
            self.subscript = subscript
        def rename(self, dst, src):
            self.array.rename(dst, src)
        def __repr__(self):
            return 'Element(%s, %s, %s)'%(self.typ, self.array, self.subscript)
    class Identifier(Value):
        def __init__(self, typ, name):
            super(TACifier.Identifier, self).__init__(typ)
            self.name = name
        def rename(self, dst, src):
            if self.name == dst:
                self.name = src
        def __repr__(self):
            return 'Identifier(%s, %s)'%(self.typ, self.name)
    class Flag(object):
        def __init__(self, flag):
            self.flag = flag
        def __repr__(self):
            return 'Flag(%s)' % (self.flag,)
    class Gensym(object):
        def __init__(self, n):
            self.n = n
        def __repr__(self):
            return '$(%d)'%(self.n,)
    class NoKill(object):
        """Wraps a Gensym to prevent it being killed.
        Used when we need the result of a subexpression more than once, e.g. for
        value writeback in an lvalue."""
        def __init__(self, g):
            self.g = g
        def __repr__(self):
            return "$'(%d)"%(self.g.n,)
        def __hash__(self):
            return hash(self.g)
        def __eq__(self, other):
            if isinstance(other, TACifier.Gensym):
                return self.g == other
            if isinstance(other, TACifier.NoKill):
                return self.g == other.g
            return False
    def nokill(self, sym):
        if isinstance(sym, self.Gensym):
            return self.NoKill(sym)
        return sym
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
        self.enums = {}
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
    def get_enum_type(self, name):
        for e,d in self.enums.items():
            for (n, v) in d.defn:
                if n == name:
                    return e
        raise TACError("Tried to get non-existent enum constant", name)
    def done(self, sym):
        if isinstance(sym.name, self.Gensym): # no-one but us has a reference to it
            del self.scopes[-1][sym.name]
    def get_lvalue(self, lval, prefer='', read=True):
        if isinstance(lval, AST.Identifier):
            for scope in reversed(self.scopes):
                if lval.ident in scope:
                    sc, typ = scope[lval.ident]
                    return (self.Identifier(typ, lval.ident), [], [])
            raise TACError("Name", lval.ident, "not in scope")
        if isinstance(lval, AST.UnaryExpr):
            if lval.op == '*':
                pointer, pa, pb = self.walk_expr(lval.arg, prefer=self.PREFER_ADDRESS)
                if not isinstance(pointer.typ, AST.Pointer):
                    raise TACError("Dereferencing non-pointer", lval.arg)
                sym = self.gensym()
                typ = pointer.typ.target
                self.scopes[-1][sym] = (AST.Auto, typ)
                pa.insert(0, self.TACDeclare(sym, AST.Auto, typ))
                if read:
                    pa.append(self.TACDeref(sym, self.nokill(pointer.name), prefer=prefer))
                post = [self.TACWrite(pointer.name, sym)]
                self.done(pointer)
                return (self.Identifier(typ, sym), pa, post + pb)
            raise NotImplementedError(lval)
        if isinstance(lval, AST.MemberExpr):
            target, ta, tb = self.walk_expr(lval.target)
            member = lval.tag
            if lval.op == '->':
                if not isinstance(target.typ, AST.Pointer):
                    raise TACError("Dereferencing (by ->) non-pointer", lval.target)
                sym = self.gensym()
                typ = self.get_member_type(target.typ.target, member)
                self.scopes[-1][sym] = (AST.Auto, typ)
                ta.insert(0, self.TACDeclare(sym, AST.Auto, typ))
                if read:
                    ta.append(self.TACMemberRead(sym, self.nokill(target.name), member))
                post = [self.TACMemberWrite(target.name, member, sym)]
                self.done(target)
                return (self.Identifier(typ, sym), ta, post + tb)
            raise NotImplementedError(lval)
        if isinstance(lval, AST.SubscriptExpr):
            target, ta, tb = self.walk_expr(lval.target)
            if isinstance(target.typ, AST.Pointer):
                etyp = target.typ.target
            elif isinstance(target.typ, AST.Array):
                etyp = target.typ.type
            else:
                raise TACError("Subscripting non-pointerish", lval.target)
            subscript, sa, sb = self.walk_expr(lval.subscript)
            if not AST.Word().compat(subscript.typ):
                raise TACError("Subscript is not integer", lval.subscript)
            pre = ta + sa
            psym = self.gensym() # we never add this to the scope
            ptyp = AST.Pointer(etyp)
            pre.insert(0, self.TACDeclare(psym, AST.Auto, ptyp))
            pre.append(self.TACAssign(psym, target.name, prefer=self.PREFER_ADDRESS))
            pre.append(self.TACAdd(psym, subscript.name))
            sym = self.gensym()
            self.scopes[-1][sym] = (AST.Auto, etyp)
            pre.insert(0, self.TACDeclare(sym, AST.Auto, etyp))
            if read:
                pre.append(self.TACDeref(sym, self.nokill(psym), prefer=prefer))
            post = [self.TACWrite(psym, sym)]
            self.done(target)
            return (self.Identifier(etyp, sym), pre, post + tb + sb)
        raise NotImplementedError(lval)
    def get_constant(self, rval):
        if isinstance(rval, AST.Identifier):
            for scope in reversed(self.scopes):
                if rval.ident in scope:
                    sc, typ = scope[rval.ident]
                    return self.Identifier(typ, rval.ident)
            raise TACError("Name", rval.ident, "not in scope")
        if isinstance(rval, AST.IntConst):
            return self.Identifier(rval.typ, rval)
        if isinstance(rval, AST.EnumConst):
            typ = self.get_enum_type(rval.name)
            return self.Identifier(typ, rval)
        raise UnhandledEntity(rval)
    def get_string_literal(self, expr, prefer=''):
        sym = self.gensym()
        typ = AST.Pointer(AST.Const(AST.Byte()))
        self.scopes[-1][sym] = (AST.Auto, typ)
        stmts = [self.TACDeclare(sym, AST.Auto, typ)]
        string = self.gensym()
        self.strings[string] = expr.text
        l = len(expr.text) + 1
        styp = AST.Array(AST.IntConst(l, True), AST.Const(AST.Byte()))
        stmts.append(self.TACDeclare(string, AST.Static, styp))
        stmts.append(self.TACAddress(sym, string, prefer=prefer))
        return (self.Identifier(typ, sym), stmts, [])
    def emit_assignish(self, op, lvalue, rvalue, prefer=''):
        if not isinstance(lvalue, self.Identifier):
            raise TACError("Uninterpreted lvalue", lvalue)
        if not isinstance(rvalue, self.Identifier):
            raise TACError("Uninterpreted rvalue", rvalue)
        if isinstance(rvalue.typ, AST.Array): # 'decay' to a pointer
            raise UnhandledEntity(rvalue) # TODO qualifiers?
            rvalue.typ = AST.Pointer(rvalue.typ.typ)
        if isinstance(lvalue.typ, AST.Pointer) and op != '=':
            if not AST.Word().compat(rvalue.typ):
                raise TACError("Type mismatch in assignment", lvalue, op, rvalue)
        elif not lvalue.typ.compat(rvalue.typ.unqualified()):
            # we unqualify it because qualifiers at top level don't matter
            raise TACError("Type mismatch in assignment", lvalue, op, rvalue)
        if op == '+=':
            return [self.TACAdd(lvalue.name, rvalue.name)]
        if op == '=':
            return [self.TACAssign(lvalue.name, rvalue.name, prefer=prefer)]
        raise NotImplementedError(op)
    def emit_return(self, rvalue):
        if self.in_func is None:
            raise TACError("return outside function")
        decl = self.in_func[1]
        typ = decl.ret
        if isinstance(rvalue, self.Identifier):
            if not typ.compat(rvalue.typ):
                raise TACError("Type mismatch returning", rvalue, "from", decl)
            return [self.TACReturn(rvalue.name)]
        raise TACError("Uninterpreted rvalue", rvalue)
    def retcon_preference(self, stmts, sym, prefer):
        if not stmts:
            # Expression was just an identifier or constant, nothing to prefer
            return
        stmts = [s for s in stmts if isinstance(s, TACAssign) and s.dst == sym]
        assert len(stmts) == 1, (stmts, sym)
        stmts[0].prefer = prefer
    def walk_expr(self, expr, prefer=''): # this always returns an rvalue
        if isinstance(expr, (AST.IntConst, AST.EnumConst, AST.Identifier)):
            return (self.get_constant(expr), [], [])
        if isinstance(expr, AST.StringLiteral):
            return self.get_string_literal(expr, prefer=prefer)
        if isinstance(expr, AST.FlagIdent):
            return (self.Identifier(AST.Bool(), self.Flag(expr.flag)), [], [])
        if isinstance(expr, AST.AssignExpr):
            lval = expr.left
            rval = expr.right
            compound = expr.op != '=' # need to read the old value
            lvalue, la, lb = self.get_lvalue(lval, prefer=prefer, read=compound)
            rvalue, ra, rb = self.walk_expr(rval)
            return (lvalue, ra + la + self.emit_assignish(expr.op, lvalue, rvalue) + lb + rb, []) # lvalue becomes an rvalue, returns the value written
        if isinstance(expr, AST.EqualityExpr):
            left, la, lb = self.walk_expr(expr.left)
            right, ra, rb = self.walk_expr(expr.right)
            sym = self.gensym() # either use in a conditional context, or assign (really Rename) to a variable
            typ = AST.Bool()
            return (self.Identifier(typ, sym), la + ra + [self.TACDeclare(sym, AST.Auto, typ),
                                                          self.TACCompare(sym, expr.op, left.name, right.name)],
                    lb + rb)
        if isinstance(expr, AST.UnaryExpr):
            if expr.op == '*':
                pointer, pa, pb = self.walk_expr(expr.arg)
                if not isinstance(pointer.typ, AST.Pointer):
                    raise TACError("Dereferencing non-pointer", expr.arg)
                sym = self.gensym()
                typ = pointer.typ.target
                self.scopes[-1][sym] = (AST.Auto, typ)
                stmts = pa
                stmts.append(self.TACDeclare(sym, AST.Auto, typ))
                stmts.append(self.TACDeref(sym, pointer.name, prefer=prefer))
                self.done(pointer)
                return (self.Identifier(typ, sym), stmts + pb, [])
            if expr.op == '&':
                if isinstance(expr.arg, AST.Identifier):
                    target = self.get_constant(expr.arg)
                    sym = self.gensym()
                    typ = AST.Pointer(target.typ)
                    self.scopes[-1][sym] = (AST.Auto, typ)
                    stmts = [self.TACDeclare(sym, AST.Auto, typ),
                             self.TACAddress(sym, target.name, prefer=prefer)]
                    return (self.Identifier(typ, sym), stmts, [])
                if isinstance(expr.arg, AST.SubscriptExpr):
                    # &A[B] ==> A + B, but A must be pointer
                    expr = expr.arg
                    target, ta, tb = self.walk_expr(expr.target)
                    if isinstance(target.typ, AST.Pointer):
                        etyp = target.typ.target
                    elif isinstance(target.typ, AST.Array):
                        etyp = target.typ.type
                    else:
                        raise TACError("Subscripting non-pointerish", expr.target)
                    # If subscript is a byte, we'll be wanting to extend it for the add
                    subscript, sa, sb = self.walk_expr(expr.subscript, prefer=self.PREFER_LOWBYTE)
                    styp = subscript.typ
                    if isinstance(styp, AST.Enum):
                        if styp.typ is None:
                            if styp.tag not in self.enums:
                                raise TACError("Subscripting with incomplete enum", styp.tag)
                            styp = self.enums[subscript.typ.tag].typ
                        else:
                            styp = styp.typ
                    if not AST.Word().compat(styp):
                        raise TACError("Subscript is not integer", expr.subscript)
                    stmts = ta + sa
                    sym = self.gensym()
                    typ = AST.Pointer(etyp)
                    stmts.insert(0, self.TACDeclare(sym, AST.Auto, typ))
                    stmts.append(self.TACAssign(sym, target.name, prefer=prefer))
                    self.done(target)
                    stmts.append(self.TACAdd(sym, subscript.name))
                    self.done(subscript)
                    return (self.Identifier(typ, sym), stmts + tb + sb, [])
                raise UnhandledEntity(expr.arg)
            raise UnhandledEntity(expr)
        if isinstance(expr, AST.PostcremExpr):
            if expr.op == '++':
                crement = 1
            elif expr.op == '--':
                crement = -1
            else: # can't happen
                raise TACError("Weird excrement op", expr) # well, what would _you_ call the set {increment, decrement}?
            lvalue, pre, post = self.get_lvalue(expr.target, prefer=prefer)
            typ = lvalue.typ
            if AST.Word().compat(typ):
                crement = typ.make(crement)
            elif isinstance(typ, AST.Pointer):
                crement = AST.Word().make(crement)
            else:
                raise TACError("Can't postcrement type", typ)
            return (lvalue, pre, [self.TACAdd(lvalue.name, crement)] + post)
        if isinstance(expr, AST.PrecremExpr):
            if expr.op == '++':
                crement = 1
            elif expr.op == '--':
                crement = -1
            else: # can't happen
                raise TACError("Weird excrement op", expr)
            lvalue, pre, post = self.get_lvalue(expr.arg, prefer=prefer)
            typ = lvalue.typ
            typ = lvalue.typ
            if AST.Word().compat(typ):
                crement = typ.make(crement)
            elif isinstance(typ, AST.Pointer):
                crement = AST.Word().make(crement)
            else:
                raise TACError("Can't precrement type", typ)
            # we choose to write back the value before returning, as it's more likely to still be in a register
            return (lvalue, pre + [self.TACAdd(lvalue.name, crement)] + post, [])
        if isinstance(expr, AST.MemberExpr):
            target, pre, post = self.walk_expr(expr.target)
            member = expr.tag
            if expr.op == '->':
                if not isinstance(target.typ, AST.Pointer):
                    raise TACError("Dereferencing (by ->) non-pointer", expr.target)
                self.retcon_preference(pre, target, self.PREFER_ADDRESS)
                sym = self.gensym()
                typ = self.get_member_type(target.typ.target, member)
                self.scopes[-1][sym] = (AST.Auto, typ)
                pre.insert(0, self.TACDeclare(sym, AST.Auto, typ))
                pre.append(self.TACMemberRead(sym, target.name, member, prefer=prefer))
                self.done(target)
                return (self.Identifier(typ, sym), pre + post, [])
            raise NotImplementedError(lval)
        if isinstance(expr, AST.RelationExpr):
            left, la, lb = self.walk_expr(expr.left)
            right, ra, rb = self.walk_expr(expr.right)
            sym = self.gensym() # either use in a conditional context, or assign (really Rename) to a variable
            typ = AST.Bool()
            return (self.Identifier(typ, sym), la + ra + [self.TACDeclare(sym, AST.Auto, typ),
                                                          self.TACCompare(sym, expr.op, left.name, right.name)],
                    lb + rb)
        if isinstance(expr, AST.SubscriptExpr):
            target, ta, tb = self.walk_expr(expr.target, prefer=self.PREFER_ADDRESS)
            if isinstance(target.typ, AST.Pointer):
                etyp = target.typ.target
            elif isinstance(target.typ, AST.Array):
                etyp = target.typ.type
            else:
                raise TACError("Subscripting non-pointerish", expr.target)
            # If subscript is a byte, we'll be wanting to extend it for the add
            subscript, sa, sb = self.walk_expr(expr.subscript, prefer=self.PREFER_LOWBYTE)
            styp = subscript.typ
            if isinstance(styp, AST.Enum):
                if styp.typ is None:
                    if styp.tag not in self.enums:
                        raise TACError("Subscripting with incomplete enum", styp.tag)
                    styp = self.enums[subscript.typ.tag].typ
                else:
                    styp = styp.typ
            if not AST.Word().compat(styp):
                raise TACError("Subscript is not integer", expr.subscript)
            stmts = ta + sa
            psym = self.gensym() # we never add this to the scope
            ptyp = AST.Pointer(etyp)
            stmts.insert(0, self.TACDeclare(psym, AST.Auto, ptyp))
            stmts.append(self.TACAssign(psym, target.name, prefer=self.PREFER_ADDRESS))
            self.done(target)
            stmts.append(self.TACAdd(psym, subscript.name))
            self.done(subscript)
            sym = self.gensym()
            self.scopes[-1][sym] = (AST.Auto, etyp)
            stmts.insert(0, self.TACDeclare(sym, AST.Auto, etyp))
            stmts.append(self.TACDeref(sym, psym, prefer=prefer))
            return (self.Identifier(etyp, sym), stmts + tb + sb, [])
        if isinstance(expr, AST.AdditiveExpr):
            left, la, lb = self.walk_expr(expr.left)
            right, ra, rb = self.walk_expr(expr.right)
            sym = self.gensym()
            lt = left.typ
            rt = right.typ
            if lt.compat(rt):
                ct = lt.common(rt)
            elif rt.compat(lt):
                ct = rt.common(lt)
            else:
                raise TACError("Tried to add incompatible types", lt, rt)
            if ct.fixed_size == 2:
                if rt.fixed_size == 1:
                    self.retcon_preference(rs, right, self.PREFER_LOWBYTE)
                elif lt.fixed_size == 1:
                    self.retcon_preference(ls, left, self.PREFER_LOWBYTE)
            if expr.op == '+':
                cls = self.TACAdd
            elif expr.op == '-':
                cls = self.TACSub
            else:
                raise TACError("No such op", expr)
            stmts = la + ra + [self.TACDeclare(sym, AST.Auto, ct),
                               self.TACAssign(sym, left.name, prefer=prefer),
                               cls(sym, right.name)]
            self.done(left)
            self.done(right)
            return (self.Identifier(ct, sym), stmts + lb + rb, [])
        if isinstance(expr, AST.CastExpr):
            arg, aa, ab = self.walk_expr(expr.arg)
            sym = self.gensym()
            stmts = aa + [self.TACDeclare(sym, AST.Auto, expr.typ),
                          self.TACAssign(sym, arg.name, prefer=prefer)]
            self.done(arg)
            return (self.Identifier(expr.typ, sym), stmts + ab, [])
        if isinstance(expr, AST.FuncallExpr):
            func, fa, fb = self.walk_expr(expr.target)
            if not isinstance(func.typ, AST.Function):
                raise TACError("Calling non-function %s, is %s" %(expr, func))
            rtyp = func.typ.ret
            if len(func.typ.params) != len(expr.args):
                raise TACError("Function %s takes %d args, passed %d" %
                               (expr.target, len(func.typ.params), len(expr.args)))
            args = []
            asa = []
            asb = []
            for p,a in zip(func.typ.params, expr.args):
                arg, aa, ab = self.walk_expr(a)
                if not p.typ.compat(arg.typ):
                    raise TACError("Parameter %s has wrong type %s for parameter %s (type %s) to %s" %
                                   (a, arg.typ, p.ident, p.typ, expr.target))
                args.append(arg)
                asa.extend(aa)
                asb.extend(ab)
            if rtyp == AST.Void():
                return (None, fa + asa + [self.TACCall(func, None, args)] + asb + fb, [])
            sym = self.gensym()
            self.scopes[-1][sym] = (LEX.Auto('auto'), rtyp)
            return (self.Identifier(rtyp, sym), [self.TACDeclare(sym, LEX.Auto('auto'), rtyp)] + fa + asa +
                                                [self.TACCall(func, sym, args)] + asb + fb, [])
        raise UnhandledEntity(expr)
    def init_list(self, init, sc, name):
        stmts = []
        for di in init.list:
            sym = name
            typ = name.typ
            for d in di.d:
                if isinstance(d, AST.MemberDesignator):
                    if not isinstance(typ, AST.Struct):
                        raise TACError("Type mismatch in initialiser", di, "expected struct for", d, "but have", typ)
                    mtyp = self.get_member_type(typ, d.tag)
                    sym = self.Member(mtyp, sym, d.tag)
                else:
                    raise UnhandledEntity(d)
            i, ia, ib = self.initialise(di.i, sc, self.gensym(), sym.typ)
            ia.append(self.TACInit(sym, i))
            stmts.extend(ia + ib)
        return (name, stmts, [])
    def initialise(self, init, sc, name, typ):
        if isinstance(init, AST.InitList):
            i, ia, ib = self.init_list(init, sc, self.Identifier(typ, name))
        else:
            i, ia, ib = self.walk_expr(init)
        if not isinstance(i, self.Identifier):
            raise TACError("Uninterpreted rvalue", i)
        if isinstance(i.name, (AST.IntConst, AST.EnumConst)):
            return i, [], []
        if isinstance(i.name, self.Gensym):
            ia.append(self.TACRename(name, i.name))
        else:
            ia.insert(0, self.TACDeclare(name, sc, typ))
            if not isinstance(init, AST.InitList):
                ia.append(self.TACAssign(name, i.name))
        return self.Identifier(typ, name), ia, ib
    def walk_stmt(self, stmt):
        if isinstance(stmt, AST.ExpressionStatement):
            rvalue, pre, post = self.walk_expr(stmt.expr)
            if rvalue is not None:
                self.done(rvalue)
            return pre + post
        elif isinstance(stmt, AST.ReturnStatement):
            rvalue, pre, post = self.walk_expr(stmt.value, prefer=self.PREFER_RETURN)
            return pre + post + self.emit_return(rvalue)
        elif isinstance(stmt, AST.LabelStatement):
            return [self.TACLabel(stmt.label)]
        elif isinstance(stmt, AST.IfStatement):
            cond, pre, post = self.walk_expr(stmt.condition)
            if stmt.false:
                raise UnhandledEntity(stmt)
            if isinstance(stmt.true, AST.GotoStatement):
                return pre + post + [self.TACCondGoto(cond.name, stmt.true.label)]
            then = self.walk_stmt(stmt.true)
            label = self.genlabel()
            return pre + post + [self.TACIf(cond.name, label)] + then + [self.TACLabel(label)]
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
            rvalue, pre, post = self.initialise(init, sc, name, decl.typ)
            if not decl.typ.compat(rvalue.typ):
                self.err("Want: %s"%(decl.typ,))
                self.err("Have: %s"%(rvalue.typ,))
                raise TACError("Initialiser for %s has wrong type"%(name,))
            stmts.extend(pre + post)
        return stmts
    def walk(self, block):
        func = []
        for declaration in block.decls:
            typ = declaration.typ
            if isinstance(typ, AST.Struct):
                func.extend(self.declare_struct(typ.tag, typ.body))
            elif isinstance(typ, AST.Enum):
                struct.extend(self.declare_enum(typ.tag, typ.typ, typ.body))
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
    def normalise_globals(self):
        self.functions[None] = self.normalise(self.functions[None])
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
                elif isinstance(typ, AST.Enum):
                    struct.extend(self.declare_enum(typ.tag, typ.typ, typ.body))
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
    def declare_enum(self, tag, typ, body):
        if body is None:
            self.enums.setdefault(tag, None)
            return []
        elif self.enums.get(tag) is None:
            enum = []
            self.scopes.append({})
            for value in body:
                en = value.name
                ev = value.value
                if ev is None:
                    enum.append((en, None))
                else:
                    enum.append((en, self.walk_expr(ev)))
            self.scopes.pop(-1)
            self.enums[tag] = self.TACEnumDef(tag, typ, enum)
            return [self.enums[tag]]
        else:
            raise TACError("enum %s redefined"%(tag,))
    def add(self, decl):
        code = self.functions[self.in_func]
        if isinstance(decl, AST.Declare):
            if isinstance(decl.typ, AST.Struct):
                body = decl.typ.body
                tag = decl.typ.tag
                code.extend(self.declare_struct(tag, body))
            elif isinstance(decl.typ, AST.Enum):
                body = decl.typ.body
                typ = decl.typ.typ
                tag = decl.typ.tag
                code.extend(self.declare_enum(tag, typ, body))
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
    def err(self, *args):
        print >>sys.stderr, ' '.join(map(str, args))
    def debug(self):
        print "TAC scopes:"
        for i,scope in enumerate(self.scopes):
            print i
            for name, (sc, typ) in scope.iteritems():
                print '\t%s %s %s' % (sc, name, typ)
        print "TAC functions:"
        pprint.pprint(self.functions)
        print "TAC strings:"
        pprint.pprint(self.strings)
        print "TAC structs:"
        pprint.pprint(self.structs)
        print "TAC enums:"
        pprint.pprint(self.enums)

## Entry point
def tacify(ast):
    tac = TACifier()
    for decl in ast.decls:
        tac.add(decl)
    tac.normalise_globals()
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
    tac = tacify(ast)
    tac.debug()
    assert tac.in_func is None, tac.in_func
    assert len(tac.scopes) == 1

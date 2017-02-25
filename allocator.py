#!/usr/bin/python

import sys, pprint
import ast_build as AST, tacifier
TAC = tacifier.TACifier

## Perform stack frame and register allocation on the TAC intermediate form
## to generate interim stack frame and RTL intermediate form

class AllocError(Exception): pass

builtin_sizes = {'bool':1, 'byte': 1, 'word': 2}

class Literal(object):
    def __init__(self, value):
        self.value = value
        self.name = None
        self.user = self
        self.isdirty = False
        self.oldl = self
    def lock(self): pass
    def unlock(self): pass
    def free(self): pass
    def __str__(self):
        return str(self.value)
    __repr__ = __str__
    def __eq__(self, other):
        return isinstance(other, Literal) and self.value == other.value
class ByteLiteral(Literal):
    size = 1
    typ = AST.Byte()
    @property
    def hi(self):
        return ByteLiteral(0)
    @property
    def lo(self):
        return self
class WordLiteral(Literal):
    size = 2
    typ = AST.Word()
    @property
    def hi(self):
        return ByteLiteral(self.value >> 8)
    @property
    def lo(self):
        return ByteLiteral(self.value & 0xFF)
class Register(object):
    def __init__(self, name):
        self.name = name
        self.user = None
        self._oldl = None # Last thing we held, if it was a literal
        self._lock = False
        self.isdirty = False
    @property
    def available(self):
        return not self.user
    def claim(self, user):
        if isinstance(user, (AST.IntConst, int)): # should be Literals
            raise AllocError("Storing", user, "in", self)
        if not self.available:
            raise AllocError("Attempted to claim %s, in use by %s"%(self, self.user))
        self.user = user
        if isinstance(user, Literal):
            self.oldl = user
        else:
            self.oldl = None
        self.isdirty = False
    @property
    def oldl(self):
        return self._oldl
    @oldl.setter
    def oldl(self, value):
        self._oldl = value
    def dirty(self):
        if not self.user:
            raise AllocError("Attempted to dirty %s, but is empty"%(self,))
        self.isdirty = True
    def clean(self):
        self.isdirty = False
    def free(self):
        if self.locked:
            raise AllocError("Attempted to free %s, locked by %s"%(self, self.user))
        if self.isdirty:
            raise AllocError("Attempted to free %s, dirty with %s"%(self, self.user))
        self.user = None
    @property
    def locked(self):
        return self._lock
    def lock(self):
        self._lock = True
    def unlock(self):
        self._lock = False
    def __str__(self):
        return self.name
    __repr__ = __str__
class ByteRegister(Register):
    size = 1
class WordRegister(Register):
    size = 2
class SplitByteRegister(ByteRegister):
    def __init__(self, name, parent):
        super(SplitByteRegister, self).__init__(name)
        self.parent = parent
    def claim(self, user):
        super(SplitByteRegister, self).claim(user)
        # We could possibly try to update it if user were a literal and
        # parent had an oldl; but that's probably not worth the trouble
        self.parent.oldl = None
    def free(self):
        if self.parent.user:
            raise AllocError("Attempted to free %s, in use by parent %s"%(self, self.parent))
        super(ByteRegister, self).free()
    @property
    def partner(self):
        return [c for c in self.parent.children if c != self][0]
    # state-functions are used for EX DE,HL
    @property
    def state(self):
        return (self.user, self.isdirty, self.oldl)
    @state.setter
    def state(self, value):
        self.user, self.isdirty, self.oldl = value
    @property
    def available(self):
        return not (self.user or self.parent.user)
    @property
    def locked(self):
        return self._lock or self.parent._lock
class SplittableRegister(WordRegister):
    def __init__(self, name, hiname=None, loname=None):
        super(SplittableRegister, self).__init__(name)
        if hiname is None:
            hiname = name[0]
        if loname is None:
            loname = name[1]
        self.hi = SplitByteRegister(hiname, self)
        self.lo = SplitByteRegister(loname, self)
        self.children = self.hi, self.lo
    @property
    def oldl(self):
        return self._oldl
    @oldl.setter
    def oldl(self, value):
        if value is None:
            # Invalidate child oldls
            self.hi.oldl = None
            self.lo.oldl = None
        else:
            # Fill in child oldls with bytes of our oldl
            self.hi.oldl = value.hi
            self.lo.oldl = value.lo
        self._oldl = value
    def free(self):
        if any(c.user for c in self.children):
            raise AllocError("Attempted to free %s, in use by child %s"%(self, c))
        super(WordRegister, self).free()
    # state-functions are used for EX DE,HL
    @property
    def state(self):
        if self.locked:
            raise AllocError("Attempted to copy state of %s while locked"%(self,))
        return (self.user, self.isdirty, self.oldl, [c.state for c in self.children])
    @state.setter
    def state(self, value):
        self.user, self.isdirty, self.oldl, d = value
        for c,v in zip(self.children, d):
            c.state = v
    @property
    def available(self):
        return not (self.user or any(c.user for c in self.children))
    @property
    def locked(self):
        return self._lock or any(c._lock for c in self.children)
class IndexRegister(SplittableRegister):
    def __init__(self, name):
        super(IndexRegister, self).__init__(name, name+'H', name+'L')
class Flag(object):
    gen_table = {'Z': ('NZ', 'Z'),
                 'C': ('NC', 'C'),
                 'V': ('PO', 'PE'),
                 'S': ('P', 'M'),
                 }
    def __init__(self, name):
        self.n = name.startswith('N')
        if self.n: name = name[1:]
        assert name in 'ZCVS', name
        self.name = name
    @property
    def neg(self):
        if self.n:
            return Flag(self.name)
        return Flag('N' + self.name)
    @property
    def gen(self):
        return self.gen_table[self.name][not self.n]
    def __repr__(self):
        n = 'N' if self.n else ''
        return '#%s%s' % (n, self.name)

class RTLStructDef(object):
    def __init__(self, name, decls):
        self.name = name
        self.decls = decls
    def allocate(self, rtl):
        assert isinstance(rtl, Allocator), rtl
        self.members = []
        self.offsets = {}
        at = 0
        for t in self.decls:
            assert isinstance(t, TAC.TACDeclare), t
            if t.typ is None: continue
            size = rtl.sizeof(t.typ)
            self.members.append((at, t.typ, t.name, size))
            self.offsets[t.name] = at
            at += size
        if at > 128:
            raise AllocError("struct", self.name, "too big", at, "exceeds limit of 128 bytes")
        self.size = at
    def __repr__(self):
        return 'RTLStructDef(%r)'%(self.decls,)

class RTLEnumDef(object):
    def __init__(self, name, typ, values):
        self.name = name
        self.typ = typ
        self.vals = values
    def allocate(self, rtl):
        assert isinstance(rtl, Allocator), rtl
        self.values = {}
        at = 0
        for (n, v) in self.vals:
            if v is not None:
                next = rtl.evaluate(v)
                if not self.typ.compat(next.typ):
                    raise AllocError("Type of value", next, "does not match enum", self.name, self.typ)
                at = next.value
            self.values[n] = at
            at += 1
    def __repr__(self):
        return 'RTLEnumDef(%s, %r)'%(self.typ, self.vals)

class Allocator(object):
    class RTLStatement(object):
        def __repr__(self):
            return '%s()'%(self.__class__.__name__,)
    class RTLReturn(RTLStatement): pass
    class RTLCall(RTLStatement):
        def __init__(self, addr):
            self.addr = addr
        def __repr__(self):
            return 'RTLCall(%r)'%(self.addr,)
    class RTLLabel(RTLStatement):
        def __init__(self, name):
            self.name = name
        def __repr__(self):
            return 'RTLLabel(%s)'%(self.name,)
    class RTLJump(RTLStatement):
        def __init__(self, label):
            self.label = label
        def __repr__(self):
            return 'RTLJump(%s)'%(self.label,)
    class RTLCJump(RTLStatement):
        def __init__(self, label, flag):
            self.label = label
            self.flag = flag
        def __repr__(self):
            return 'RTLCJump(%s, %r)'%(self.label, self.flag)
    class RTLSpill(RTLStatement):
        def __init__(self, reg, name):
            self.reg = reg
            self.name = name
        def __repr__(self):
            return 'RTLSpill(%s, %r)'%(self.reg, self.name)
    class RTLFill(RTLStatement):
        def __init__(self, reg, name):
            self.reg = reg
            self.name = name
        def __repr__(self):
            return 'RTLFill(%s, %r)'%(self.reg, self.name)
    class RTLMove(RTLStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def __repr__(self):
            return 'RTLMove(%s, %s)'%(self.dst, self.src)
    class RTLPush(RTLStatement):
        def __init__(self, src):
            self.src = src
        def __repr__(self):
            return 'RTLPush(%s)'%(self.src,)
    class RTLPop(RTLStatement):
        def __init__(self, dst):
            self.dst = dst
        def __repr__(self):
            return 'RTLPop(%s)'%(self.dst,)
    class RTLExchange(RTLStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def __repr__(self):
            return 'RTLExchange(%s, %s)'%(self.dst, self.src)
    class RTLAddress(RTLStatement):
        # For auto (stack) values.  static ones can be addressed statically
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def __repr__(self):
            return 'RTLAddress(%s, %s)'%(self.dst, self.src)
    class RTLDeref(RTLStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def __repr__(self):
            return 'RTLDeref(%s, %s)'%(self.dst, self.src)
    class RTLWrite(RTLStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def __repr__(self):
            return 'RTLWrite(%s, %s)'%(self.dst, self.src)
    class RTLIndirectRead(RTLStatement):
        def __init__(self, dst, src, offset):
            self.dst = dst
            self.src = src
            self.offset = offset
        def __repr__(self):
            return 'RTLIndirectRead(%s, %s, %d)'%(self.dst, self.src, self.offset)
    class RTLIndirectWrite(RTLStatement):
        def __init__(self, dst, offset, src):
            self.dst = dst
            self.offset = offset
            self.src = src
        def __repr__(self):
            return 'RTLIndirectWrite(%s, %d, %s)'%(self.dst, self.offset, self.src)
    class RTLIndirectInit(RTLStatement):
        def __init__(self, dst, offset, src):
            self.dst = dst # name of a symbol
            self.offset = offset
            self.src = src
        def __repr__(self):
            return 'RTLIndirectInit(%s, %d, %s)'%(self.dst, self.offset, self.src)
    class RTLAnd(RTLStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def __repr__(self):
            return 'RTLAnd(%s, %s)'%(self.dst, self.src)
    class RTLAdd(RTLStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def __repr__(self):
            return 'RTLAdd(%s, %s)'%(self.dst, self.src)
    class RTLCp(RTLStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def __repr__(self):
            return 'RTLCp(%s, %s)'%(self.dst, self.src)
    def __init__(self, func, name, tac, w_opts, outer=None):
        self.name = name
        self.tac = tac
        globs = tac.scopes[0]
        if name is None:
            decl = None
            sc = None
        else:
            if name not in globs:
                raise AllocError(name, "not in global scope")
            sc, decl = globs[name]
        self.func = func
        self.sc = sc or AST.Auto
        self.decl = decl
        self.names = dict((name, (AST.Extern, typ)) for name, (sc, typ) in globs.items())
        self.stack = {}
        self.sp = 0
        self.static = {}
        self.registers = [ByteRegister('A'),
                          SplittableRegister('BC'), SplittableRegister('DE'), SplittableRegister('HL'),
                          IndexRegister('IX'), IndexRegister('IY')]
        self.general_byte_registers = [self.register(n) for n in 'BCDEHL']
        self.general_word_registers = self.registers[1:4]
        self.all_byte_registers = [self.registers[0]] + self.general_byte_registers
        self.flags = (None, None) # (symbol (of bool type) currently stored in flags, flag it's stored in)
        self.code = []
        self.structs = {}
        self.enums = {}
        self.werror = w_opts.get('error', False)
        self.wfunc_void = w_opts.get('func-void', True)
        self.has_error = False
        if outer:
            self.structs.update(outer.structs)
            self.enums.update(outer.enums)
    def evaluate(self, t):
        # t is a TAC rvalue
        sym, pre, post = t
        if pre or post:
            raise AllocError("Unhandled constant-expression", t)
        assert isinstance(sym, TAC.Identifier), t
        assert isinstance(sym.name, AST.IntConst), t
        return sym.name
    def register(self, name):
        for r in self.registers:
            if r.name == name: return r
            if isinstance(r, SplittableRegister):
                for c in r.children:
                    if c.name == name: return c
        raise AllocError("No such register", name)
    def sizeof(self, typ):
        # Discard any qualifiers
        typ = typ.unqualified()
        if typ.fixed_size is not None:
            return typ.fixed_size
        if isinstance(typ, AST.Struct):
            if typ.tag in self.structs:
                return self.structs[typ.tag].size
            raise AllocError("Incomplete struct type", typ.tag)
        if isinstance(typ, AST.Enum):
            if typ.tag in self.enums:
                return self.sizeof(self.enums[typ.tag].typ)
            raise AllocError("Incomplete enum type", typ.tag)
        if isinstance(typ, AST.Array):
            esiz = self.sizeof(typ.type)
            if isinstance(typ.dim, AST.IntConst):
                dim = typ.dim.value
            elif isinstance(typ.dim, AST.EnumConst):
                dtyp = self.tac.get_enum_type(typ.dim.name)
                if dtyp not in self.enums:
                    raise AllocError("Incomplete enum type", typ.dim.tag, "in array dimension")
                edef = self.enums[dtyp].values
                if typ.dim.name not in edef: # can't happen
                    raise AllocError("Enum type mismatch", typ.dim.name, "is not a value for", dtyp, "in array dimension")
                dim = edef[typ.dim.name]
            else:
                raise AllocError("Could not size array", typ)
            return esiz * dim
        raise NotImplementedError("sizeof", typ)
        if isinstance(typ, PAR.Pointer):
            return 2
        if isinstance(typ, PAR.Array):
            esiz = self.sizeof(typ.pointee)
            return esiz * typ.n
    def is_on_stack(self, name):
        return name in self.stack
    def spill(self, r, ignorelocal=False, leave=None):
        if r.user:
            name = r.user
            if isinstance(name, Literal):
                r.user = None # nothing to spill
                return
            assert name in self.names, name
            if ignorelocal and name in self.stack:
                r.clean() # it's local and we're not going to need it again
            if name == leave: # we don't want to spill this, we need it
                return
            if r.isdirty:
                if name in self.stack:
                    sp, typ, size, filled, spilled = self.stack[name]
                    self.stack[name] = sp, typ, size, filled, True
                # do the spill
                self.code.append(self.RTLSpill(r, name))
                r.clean()
            r.free()
        elif isinstance(r, SplittableRegister):
            for c in r.children:
                if c.user:
                    self.spill(c, ignorelocal, leave=leave)
        elif isinstance(r, SplitByteRegister):
            self.spill(r.parent, ignorelocal, leave=leave)
        else:
            raise AllocError("Spilling empty register", r)
    def find_old_byte(self, l):
        if isinstance(l, (AST.IntConst, AST.EnumConst)):
            # Convert to ByteLiteral
            l = self.fetch_src_byte(l)
        for r in self.all_byte_registers:
            if r.oldl == l:
                return r
    def find_old_word(self, l):
        if isinstance(l, (AST.IntConst, AST.EnumConst)):
            # Convert to WordLiteral
            l = self.fetch_src_word(l)
        for r in self.all_word_registers:
            if r.oldl == l:
                return r
    def fill(self, r, name):
        if isinstance(name, AST.IntConst):
            if name.long:
                name = WordLiteral(name.value)
            else:
                name = ByteLiteral(name.value)
        assert name in self.names or isinstance(name, Literal), name
        # is it currently in flags?
        if self.flags[0] == name:
            assert r == self.register('A')
            # materialise it
            self.clobber_flag_register()
        if r.user == name: # Nothing to do; we're already filled
            return
        if r.oldl == name: # Just rematerialise the label
            if r.isdirty:
                self.spill(r)
            r.free()
            r.claim(name)
            return
        assert r.available, (r, r.user, name)
        if name in self.stack:
            sp, typ, size, filled, spilled = self.stack[name]
            self.stack[name] = sp, typ, size, True, spilled
        if isinstance(name, ByteLiteral):
            s = self.find_old_byte(name)
        elif isinstance(name, WordLiteral):
            s = self.find_old_word(name)
        else:
            s = None
        if s:
            self.move(r, s)
        else:
            self.code.append(self.RTLFill(r, name))
        r.claim(name)
    def kill(self, name):
        for r in self.all_byte_registers + self.general_word_registers:
            if r.user == name:
                r.clean()
                r.free()
        if self.flags[0] == name:
            self.flags = (None, None)
    def choose_byte_register(self, spill=True, prefer=''):
        # Default preference rules:
        # prefer BCDEHL (prefer a reg whose partner is in use), then A, then spill from BCDEHL
        if prefer == TAC.PREFER_RETURN:
            # Try A first
            a = self.register('A')
            if a.available:
                return a
        if prefer == TAC.PREFER_LOWBYTE:
            # Try CEL first, partner free
            for r in self.general_word_registers:
                if r.available:
                    return r.lo
        for r in self.general_byte_registers:
            if r.available and not r.partner.available:
                return r
        for r in self.general_byte_registers:
            if r.available:
                return r
        a = self.register('A')
        if a.available:
            return a
        if not spill: return
        if prefer == TAC.PREFER_RETURN:
            # Prefer A
            if not a.locked:
                self.spill(a)
                return a
        if prefer == TAC.PREFER_LOWBYTE:
            # Try CEL, partner unlocked
            for r in self.general_word_registers:
                if not r.locked:
                    return r.lo
        for r in self.general_byte_registers:
            if not r.locked:
                self.spill(r)
                return r
        raise AllocError("Tried to choose byte reg but all are locked")
    def choose_word_register(self, spill=True, prefer=''):
        # By default, implicitly prefers BC > DE > HL
        hl = self.register('HL')
        if prefer in (TAC.PREFER_RETURN, TAC.PREFER_ADDRESS):
            # prefer HL
            if hl.available:
                return hl
        for r in self.general_word_registers:
            if r.available:
                return r
        if not spill: return
        if prefer in (TAC.PREFER_RETURN, TAC.PREFER_ADDRESS):
            # prefer HL
            if not hl.locked:
                self.spill(hl)
                return hl
        for r in self.general_word_registers:
            if not r.locked:
                self.spill(r)
                return r
        raise NotImplementedError("Can't spill, all locked")
    def fetch_src_byte(self, src, prefer=''):
        if isinstance(src, AST.IntConst):
            if src.long:
                raise AllocError("Wrong size:", src, "is long literal")
            return ByteLiteral(src.value)
        if isinstance(src, AST.EnumConst):
            typ = self.tac.get_enum_type(src.name)
            if typ not in self.enums:
                raise AllocError("Enum constant not found", src)
            if not AST.Byte().compat(self.enums[typ].typ):
                raise AllocError("Wrong size:", src, "is long enum const")
            edef = self.enums[typ].values
            if src.name not in edef: # can't happen
                raise AllocError("Enum type mismatch", src.name, "is not a value for", typ)
            return ByteLiteral(edef[src.name])
        if src not in self.names:
            raise AllocError("Name not found", src)
        sc, typ = self.names[src]
        size = self.sizeof(typ)
        if size != 1:
            raise AllocError("Wrong size:", src, "is", typ, "of size", size)
        # is it already in a register?
        reg = self.reg_find_byte(src)
        if reg is None:
            # no; we'll have to load it into one
            if self.is_on_stack(src):
                reg = self.choose_byte_register(prefer=prefer)
            else: # LD A,(nn)
                reg = self.free_a(src)
            self.fill(reg, src)
        return reg
    def fetch_src_word(self, src, prefer=''):
        if isinstance(src, AST.IntConst):
            # cast it to word
            return WordLiteral(src.value)
        if isinstance(src, AST.EnumConst):
            typ = self.tac.get_enum_type(src.name)
            if typ not in self.enums:
                raise AllocError("Enum constant not found", src)
            if not AST.Word().compat(self.enums[typ].typ): # can't happen
                raise AllocError("Type mismatch:", src, "is non-integer")
            edef = self.enums[typ].values
            if src.name not in edef: # can't happen
                raise AllocError("Enum type mismatch", src.name, "is not a value for", typ)
            return WordLiteral(edef[src.name])
        if src not in self.names:
            raise AllocError("Name not found", src)
        sc, typ = self.names[src]
        if isinstance(typ, AST.Array):
            # decay it to a pointer
            typ = AST.Pointer(typ.type)
        size = self.sizeof(typ)
        if size == 1:
            r = self.fetch_src_byte(src, prefer=TAC.PREFER_LOWBYTE)
            if isinstance(r, SplitByteRegister) and r == r.parent.lo and r.parent.hi.available:
                # Zero-extend into the parent
                reg = r.parent
                s = reg.hi
                self.fill(s, ByteLiteral(0))
                r.free()
                s.free()
                reg.claim(src)
            else:
                reg = self.choose_word_register(prefer=prefer)
                self.move(reg, r)
        elif size == 2:
            # is it already in a register?
            reg = self.reg_find_word(src)
            if reg is None:
                # no; we'll have to load it into one
                if self.is_on_stack(src):
                    reg = self.choose_word_register(prefer=prefer)
                else: # have to go via LD HL,(nn)
                    reg = self.free_hl(src)
                self.fill(reg, src)
        else:
            raise AllocError("Wrong size:", src, "is", typ, "of size", size)
        return reg
    def reg_find_byte(self, name):
        if isinstance(name, (AST.IntConst, AST.EnumConst)):
            # Convert to ByteLiteral
            name = self.fetch_src_byte(name)
        if isinstance(name, ByteLiteral):
            return name
        assert name in self.names, name
        for r in self.all_byte_registers:
            if r.user == name:
                return r
        return
    def reg_find_word(self, name):
        if isinstance(name, (AST.IntConst, AST.EnumConst)):
            # Convert to WordLiteral
            name = self.fetch_src_word(name)
        if isinstance(name, Literal):
            return name
        assert name in self.names, name
        for r in self.registers:
            if r.user == name:
                return r
        return
    def move(self, dst, src):
        dst.claim(src.user)
        dst.oldl = src.oldl
        self.code.append(self.RTLMove(dst, src))
        if src.isdirty:
            dst.dirty()
            src.clean()
        src.free()
    def copy_oldl(self, dst, src):
        dst.claim(src.oldl)
        self.code.append(self.RTLMove(dst, src))
    def free_a(self, name):
        a = self.register('A')
        if a.user != name:
            if not a.available:
                move = self.choose_byte_register(False)
                if move:
                    self.move(move, a)
                else:
                    self.spill(a)
        return a
    def free_hl(self, name):
        hl = self.register('HL')
        if hl.user != name:
            if not hl.available:
                move = self.choose_word_register(False)
                if move:
                    self.move(move, hl)
                else:
                    self.spill(hl)
        return hl
    def load_byte_into_a(self, name, try_move=True):
        if isinstance(name, (AST.IntConst, AST.EnumConst)):
            # Convert to ByteLiteral
            name = self.fetch_src_byte(name)
        a = self.register('A')
        if a.user != name:
            if a.oldl == name: # Just rematerialise the label
                self.fill(a, name)
                return a
            if not a.available:
                if try_move:
                    move = self.choose_byte_register(False)
                else:
                    move = None
                if move:
                    self.move(move, a)
                else:
                    self.spill(a)
            r = self.find_old_byte(name)
            if r:
                self.copy_oldl(a, r)
            else:
                r = self.reg_find_byte(name)
                if r:
                    self.move(a, r)
                else:
                    self.fill(a, name)
        return a
    def load_word_into_hl(self, name):
        if isinstance(name, (AST.IntConst, AST.EnumConst)):
            # Convert to WordLiteral
            name = self.fetch_src_word(name)
        hl = self.register('HL')
        if hl.user != name:
            if not hl.available: # don't bother trying to move, just spill it
                self.spill(hl)
            r = self.reg_find_word(name)
            if r: # move it to HL
                self.move(hl, r)
            else:
                self.fill(hl, name)
        return hl
    def load_word_into_ix(self, name):
        if isinstance(name, (AST.IntConst, AST.EnumConst)):
            # Convert to WordLiteral
            name = self.fetch_src_word(name)
        ix = self.register('IX')
        if ix.user != name:
            if not ix.available: # don't bother trying to move, just spill it
                self.spill(ix)
            r = self.fetch_src_word(name)
            if r: # move it to IX
                self.move(ix, r)
            else:
                self.fill(ix, name)
        return ix
    def tac_to_rtl(self, t):
        def kill_p(sym):
            return isinstance(sym, (TAC.Gensym, AST.IntConst, AST.EnumConst))
        if isinstance(t, TAC.TACDeclare): return
        if isinstance(t, TAC.TACAssign):
            if t.dst not in self.names:
                raise AllocError("Name not found", t.dst)
            sc, typ = self.names[t.dst]
            size = self.sizeof(typ)
            if size == 1:
                s = self.fetch_src_byte(t.src, prefer=t.prefer)
                r = self.reg_find_byte(t.dst)
                if r is None:
                    d = s.isdirty
                    if kill_p(t.src):
                        self.kill(t.src)
                    if isinstance(s, Literal) or s.isdirty: # load-immediate, or copy
                        r = self.choose_byte_register(prefer=t.prefer)
                        r.claim(t.dst)
                    else: # rename
                        s.free()
                        s.claim(t.dst)
                        if d:
                            s.dirty()
                        return
                r.oldl = s.oldl
                self.code.append(self.RTLMove(r, s))
                r.dirty()
                if kill_p(t.src):
                    self.kill(t.src)
                return
            elif size == 2:
                s = self.fetch_src_word(t.src, prefer=t.prefer)
                r = self.reg_find_word(t.dst)
                if r is None:
                    d = s.isdirty
                    if kill_p(t.src):
                        self.kill(t.src)
                    if isinstance(s, Literal) or s.isdirty: # load-immediate, or copy
                        r = self.choose_word_register(prefer=t.prefer)
                        r.claim(t.dst)
                    else: # rename
                        s.free()
                        s.claim(t.dst)
                        if d:
                            s.dirty()
                        return
                self.code.append(self.RTLMove(r, s))
                r.dirty()
                if kill_p(t.src):
                    self.kill(t.src)
                return
            else:
                raise AllocError("Tried to move an aggregate, size = %d"%(size,))
        if isinstance(t, TAC.TACAddress):
            r = self.reg_find_word(t.dst)
            if r is None:
                r = self.choose_word_register(prefer=t.prefer)
                r.claim(t.dst)
            if self.is_on_stack(t.src):
                # its address has been taken, it must have backing storage
                sp, typ, size, filled, spilled = self.stack[t.src]
                self.stack[t.src] = sp, typ, size, True, True
                self.code.append(self.RTLAddress(r, t.src))
            else:
                # it's static
                self.code.append(self.RTLMove(r, t.src))
            r.dirty()
            return
        if isinstance(t, TAC.TACAdd):
            if t.dst not in self.names:
                raise AllocError("Name not found", t.dst)
            sc, typ = self.names[t.dst]
            size = self.sizeof(typ)
            if size == 1: # dst has to be in A
                a = self.load_byte_into_a(t.dst)
                a.lock()
                r = self.fetch_src_byte(t.src)
                self.clobber_flag_register()
                self.code.append(self.RTLAdd(a, r))
                a.dirty()
                a.unlock()
            elif size == 2: # dst has to be in HL, src has to be in a register (even if literal).  EXCEPT if src is +/- 1, in which case we can INC/DEC
                if isinstance(t.src, AST.IntConst):
                    if t.src.value in [1, -1]:
                        r = self.fetch_src_word(t.dst)
                        s = self.fetch_src_word(t.src)
                        self.code.append(self.RTLAdd(r, s))
                        r.dirty()
                        return
                    hl = self.load_word_into_hl(t.dst)
                    hl.lock()
                    r = self.choose_word_register()
                    self.fill(r, t.src)
                    self.clobber_flag_register()
                    self.code.append(self.RTLAdd(hl, r))
                    hl.dirty()
                    hl.unlock()
                    r.clean()
                    r.free()
                    return
                hl = self.load_word_into_hl(t.dst)
                hl.lock()
                r = self.fetch_src_word(t.src)
                self.clobber_flag_register()
                self.code.append(self.RTLAdd(hl, r))
                hl.dirty()
                hl.unlock()
            else:
                raise AllocError("Tried to add to an aggregate, size = %d"%(size,))
            if kill_p(t.src):
                self.kill(t.src)
            return
        if isinstance(t, TAC.TACReturn):
            if t.src is not None: # else return type is void and there's nothing to return
                if isinstance(t.src, AST.IntConst):
                    typ = t.src.typ
                else:
                    if t.src not in self.names:
                        raise AllocError("Name not found", t.src)
                    _, typ = self.names[t.src]
                size = self.sizeof(typ)
                if size == 1: # return in A
                    # No point trying to avoid spills, we're about to return
                    self.load_byte_into_a(t.src, try_move=False)
                elif size == 2: # return in HL
                    self.load_word_into_hl(t.src)
                else:
                    raise NotImplementedError(size)
            # Spill all dirty (non-local) variables before function return
            for r in self.registers:
                if not r.available:
                    self.spill(r, ignorelocal=True)
            self.code.append(self.RTLReturn())
            return
        if isinstance(t, TAC.TACDeref):
            if t.dst not in self.names:
                raise AllocError("Name not found", t.dst)
            dsc, dtyp = self.names[t.dst]
            if t.src not in self.names:
                raise AllocError("Name not found", t.src)
            ssc, styp = self.names[t.src]
            if not isinstance(styp, AST.Pointer):
                raise AllocError("Not of pointer type", t.src, styp)
            p = self.reg_find_word(t.src)
            if isinstance(dtyp, AST.Array):
                dtyp = AST.Pointer.make(dtyp.type)
            size = self.sizeof(dtyp)
            self.kill(t.dst) # we're about to overwrite it
            if size == 1:
                if p == self.register('HL'):
                    # LD r,(HL)
                    p.lock() # don't try to use H or L
                    r = self.choose_byte_register()
                    r.claim(t.dst) # no need to fill, as we're assigning to it
                    p.unlock()
                elif p: # BC or DE
                    # LD A,(pp)
                    r = self.register('A')
                    if not r.available:
                        self.spill(r)
                    r.claim(t.dst) # no need to fill, as we're assigning to it
                elif self.register('HL').available:
                    # LD r,(HL)
                    p = self.register('HL')
                    self.fill(p, t.src)
                    p.lock() # don't try to use H or L
                    r = self.choose_byte_register()
                    r.claim(t.dst) # no need to fill, as we're assigning to it
                    p.unlock()
                elif self.register('A').available:
                    # LD A,(pp)
                    r = self.register('A')
                    r.claim(t.dst) # no need to fill, as we're assigning to it
                    p = self.choose_word_register(prefer=t.prefer)
                    self.fill(p, t.src)
                else:
                    raise NotImplementedError(p)
            elif size == 2:
                hl = self.register('HL')
                if p == self.register('BC'):
                    # PUSH/POP to shunt it into HL
                    if not hl.available:
                        self.spill(hl)
                    self.move(hl, p)
                    p = hl
                elif p == self.register('DE'):
                    p = self.exdehl(p)
                elif not p:
                    if not hl.available:
                        self.spill(hl)
                    self.fill(hl, t.src)
                    p = hl
                assert p == hl, p
                # LD r,(HL)
                p.lock() # don't try to use H or L
                r = self.choose_word_register(prefer=t.prefer)
                r.claim(t.dst) # no need to fill, as we're assigning to it
                p.unlock()
            else:
                raise AllocError("Bad size", size, "for dst of", t)
            self.code.append(self.RTLDeref(r, p))
            if kill_p(t.src):
                self.kill(t.src)
            r.dirty()
            return
        if isinstance(t, TAC.TACWrite):
            if t.dst not in self.names:
                raise AllocError("Name not found", t.dst)
            dsc, dtyp = self.names[t.dst]
            if t.src not in self.names:
                raise AllocError("Name not found", t.src)
            ssc, styp = self.names[t.src]
            if not isinstance(dtyp, AST.Pointer):
                raise AllocError("Not of pointer type", t.dst, dtyp)
            p = self.reg_find_word(t.dst)
            size = self.sizeof(styp)
            if size == 1:
                r = self.reg_find_byte(t.src)
                if (p == self.register('HL')):
                    # LD (HL),r
                    if not r:
                        p.lock() # don't try to use H or L
                        r = self.fetch_src_byte(t.src)
                        p.unlock()
                elif (r == self.register('A')):
                    # LD (pp),A
                    if not p:
                        raise NotImplementedError(r, p)
                elif r and r.name not in 'HL':
                    r.lock()
                    # LD (HL),r
                    if p == self.register('DE'):
                        p = self.exdehl(p)
                    elif p:
                        assert p == self.register('BC'), p
                        # shunt it into HL
                        hl = self.free_hl(t.dst)
                        self.move(hl, p)
                        p = hl
                    else:
                        # get it in HL
                        p = self.load_word_into_hl(t.dst)
                    r.unlock()
                elif p:
                    # LD (pp),A
                    raise NotImplementedError(r, p)
                elif self.register('HL').available: # r must be None (else r.name in 'HL', contra)
                    # LD r,(HL)
                    if r:
                        raise NotImplementedError(r, p)
                    p = self.register('HL')
                    self.fill(p, t.dst)
                    p.lock() # don't try to use H or L
                    r = self.fetch_src_byte(t.src)
                    p.unlock()
                elif self.register('A').available and not r:
                    # LD (pp),A
                    r = self.free_a()
                    self.fill(r, t.src)
                    p = self.choose_word_register(prefer=t.prefer)
                    self.fill(p, t.src)
                else:
                    raise NotImplementedError(r, p)
                self.code.append(self.RTLWrite(p, r))
            else:
                r = self.reg_find_word(t.src)
                raise NotImplementedError(size)
            if kill_p(t.src):
                self.kill(t.src)
            if kill_p(t.dst):
                self.kill(t.dst)
            return
        if isinstance(t, TAC.TACCall):
            # CALLING SEQUENCE
            # IX := IY
            # IX += caller-stack-size
            # build callee initial stack frame through (IX+d)
            # spill everything
            # PUSH IY
            # IY := IX
            # CALL (clobbers registers)
            # POP IY
            ix = self.register('IX')
            iy = self.register('IY')
            self.code.append(self.RTLMove(ix, iy))
            hl = self.register('HL')
            hl.lock() # can't use HL, we need something we can add to IX
            css = self.choose_word_register()
            hl.unlock()
            self.code.append(self.RTLIndirectRead(css.lo, iy, -1))
            self.code.append(self.RTLFill(css.hi, ByteLiteral(0)))
            self.clobber_flag_register()
            self.code.append(self.RTLAdd(ix, css))
            csp = 0 # callee stack pointer
            for arg in t.args:
                size = self.sizeof(arg.typ)
                if size == 2:
                    r = self.fetch_src_word(arg.name)
                    self.code.append(self.RTLIndirectWrite(ix, csp, r))
                else:
                    raise NotImplementedError(size)
                csp += size
                if kill_p(arg):
                    self.kill(arg)
            self.code.append(self.RTLIndirectWrite(ix, -1, ByteLiteral(csp)))
            # Spill all dirty variables before function call
            for r in self.registers:
                if not r.available:
                    self.spill(r)
            self.code.append(self.RTLPush(iy))
            self.code.append(self.RTLMove(iy, ix))
            if self.is_on_stack(t.func.name):
                raise NotImplementedError(t)
            else:
                self.code.append(self.RTLCall(t.func.name))
            self.clobber_registers()
            self.code.append(self.RTLPop(iy))
            if t.ret is not None: # bind name with return value
                rtyp = t.ret.type
                rsiz = self.sizeof(rtyp)
                print rsiz
                raise NotImplementedError(rsiz)
            return
        if isinstance(t, TAC.TACCompare):
            if t.left not in self.names:
                raise AllocError("Name not found", t.left)
            sc, typ = self.names[t.left]
            size = self.sizeof(typ)
            if size == 1: # left has to be in A
                swap = False
                if t.op == '==':
                    flag = 'Z'
                elif t.op == '<':
                    flag = 'C'
                else:
                    raise NotImplementedError(t.op)
                left, right = (t.right, t.left) if swap else (t.left, t.right)
                r = self.fetch_src_byte(right)
                r.lock()
                if r.name == 'A': # have to shunt it out of the way
                    s = self.choose_byte_register()
                    r.unlock()
                    self.move(s, r)
                    r = s
                    r.lock()
                a = self.load_byte_into_a(left)
                r.unlock()
                self.clobber_flag_register()
                self.code.append(self.RTLCp(a, r))
                self.flags = (t.dst, Flag(flag))
                if kill_p(t.left):
                    self.kill(t.left)
                if kill_p(t.right):
                    self.kill(t.right)
                return
            raise NotImplementedError(size)
        if isinstance(t, TAC.TACLabel):
            self.clobber_registers()
            self.code.append(self.RTLLabel(self.wraplabel(t.name)))
            return
        if isinstance(t, TAC.TACIf):
            if isinstance(t.cond, TAC.Flag):
                self.code.append(self.RTLCJump(self.wraplabel(t.label), Flag(t.cond.flag).neg))
                return
            if t.cond not in self.names:
                raise AllocError("Name not found", t.cond)
            sc, typ = self.names[t.cond]
            size = self.sizeof(typ)
            # spill all registers
            self.clobber_registers(leave=t.cond)
            if typ == AST.Bool() and self.flags[0] == t.cond:
                flag = self.flags[1]
                if kill_p(t.cond):
                    self.kill(t.cond)
                self.clobber_registers()
                self.code.append(self.RTLCJump(self.wraplabel(t.label), flag.neg))
                return
            if size == 1: # cond has to be in A
                a = self.load_byte_into_a(t.cond)
                self.code.append(self.RTLAnd(a, a))
                self.clobber_registers()
                self.code.append(self.RTLCJump(self.wraplabel(t.label), Flag('Z')))
                return
            raise NotImplementedError(size)
        if isinstance(t, TAC.TACCondGoto):
            if isinstance(t.cond, TAC.Flag):
                self.code.append(self.RTLCJump(self.wraplabel(t.label), Flag(t.cond.flag)))
                return
            if t.cond not in self.names:
                raise AllocError("Name not found", t.cond)
            sc, typ = self.names[t.cond]
            size = self.sizeof(typ)
            # spill all registers
            self.clobber_registers(leave=t.cond)
            if typ == AST.Bool() and self.flags[0] == t.cond:
                flag = self.flags[1]
                if kill_p(t.cond):
                    self.kill(t.cond)
                self.clobber_registers()
                self.code.append(self.RTLCJump(self.wraplabel(t.label), flag))
                return
            if size == 1: # cond has to be in A
                a = self.load_byte_into_a(t.cond)
                self.code.append(self.RTLAnd(a, a))
                self.clobber_registers()
                self.code.append(self.RTLCJump(self.wraplabel(t.label), Flag('NZ')))
                return
            raise NotImplementedError(size)
        if isinstance(t, TAC.TACGoto):
            # spill all registers
            self.clobber_registers()
            self.code.append(self.RTLJump(self.wraplabel(t.label)))
            return
        if isinstance(t, TAC.TACMemberRead):
            if t.src not in self.names:
                raise AllocError("Name not found", t.src)
            ptyp = self.names[t.src][1]
            if not isinstance(ptyp, AST.Pointer):
                raise AllocError(t.src, "is not a pointer")
            styp = ptyp.target
            if not isinstance(styp, AST.Struct):
                raise AllocError("*", t.src, "is not a struct")
            struct = self.structs[styp.tag]
            offset = struct.offsets[t.tag]
            if t.dst not in self.names:
                raise AllocError("Name not found", t.dst)
            dtyp = self.names[t.dst][1]
            size = self.sizeof(dtyp)
            ix = self.load_word_into_ix(t.src)
            self.kill(t.dst) # we're about to overwrite it
            # don't need to lock IX as nothing ever chooses it
            if size == 1:
                r = self.choose_byte_register(prefer=t.prefer)
                r.claim(t.dst)
                self.code.append(self.RTLIndirectRead(r, ix, offset))
            elif size == 2:
                hl = self.register('HL')
                hl.lock() # can't use HL with IX
                r = self.choose_word_register(prefer=t.prefer)
                hl.unlock()
                r.claim(t.dst)
                self.code.append(self.RTLIndirectRead(r, ix, offset))
            else:
                raise NotImplementedError(size, t)
            if kill_p(t.src):
                self.kill(t.src)
            return
        if isinstance(t, TAC.TACMemberWrite):
            if t.src not in self.names:
                raise AllocError("Name not found", t.src)
            styp = self.names[t.src][1]
            size = self.sizeof(styp)
            if t.dst not in self.names:
                raise AllocError("Name not found", t.dst)
            ptyp = self.names[t.dst][1]
            if not isinstance(ptyp, AST.Pointer):
                raise AllocError(t.dst, "is not a pointer")
            dtyp = ptyp.target
            if not isinstance(dtyp, AST.Struct):
                raise AllocError("*", t.dst, "is not a struct")
            struct = self.structs[dtyp.tag]
            offset = struct.offsets[t.tag]
            ix = self.load_word_into_ix(t.dst)
            # don't need to lock IX as nothing ever chooses it
            if size == 1:
                r = self.fetch_src_byte(t.src)
                self.code.append(self.RTLIndirectWrite(ix, offset, r))
            elif size == 2:
                hl = self.register('HL')
                hl.lock() # can't use HL with IX
                r = self.fetch_src_word(t.src) # but it might already be in HL
                hl.unlock()
                if r.name == 'HL': # in which case let's move it
                    r = self.exdehl(r)
                self.code.append(self.RTLIndirectWrite(ix, offset, r))
            else:
                raise NotImplementedError(size, t)
            if kill_p(t.src):
                self.kill(t.src)
            if kill_p(t.dst):
                self.kill(t.dst)
            return
        if isinstance(t, TAC.TACMemberGet):
            if t.src not in self.names:
                raise AllocError("Name not found", t.src)
            styp = self.names[t.src][1]
            if not isinstance(styp, AST.Struct):
                raise AllocError(t.src, "is not a struct")
            # this Get constitutes a fill from the struct
            if t.src in self.stack:
                sp, typ, size, filled, spilled = self.stack[t.src]
                assert typ == styp, self.stack[t.src]
                self.stack[t.src] = sp, typ, size, True, spilled
            struct = self.structs[styp.tag]
            offset = struct.offsets[t.tag]
            if t.dst not in self.names:
                raise AllocError("Name not found", t.dst)
            dtyp = self.names[t.dst][1]
            size = self.sizeof(dtyp)
            self.kill(t.dst) # we're about to overwrite it
            # don't need to lock IX/IY as nothing ever chooses them
            if size == 1:
                r = self.choose_byte_register(prefer=t.prefer)
                r.claim(t.dst)
                self.code.append(self.RTLIndirectRead(r, t.src, offset))
            elif size == 2:
                hl = self.register('HL')
                hl.lock() # can't use HL with IX/IY
                r = self.choose_word_register(prefer=t.prefer)
                hl.unlock()
                r.claim(t.dst)
                self.code.append(self.RTLIndirectRead(r, t.src, offset))
            else:
                raise NotImplementedError(size, t)
            if kill_p(t.src):
                self.kill(t.src)
            return
        if isinstance(t, TAC.TACMemberPut):
            if t.dst not in self.names:
                raise AllocError("Name not found", t.dst)
            dtyp = self.names[t.dst][1]
            if not isinstance(dtyp, AST.Struct):
                raise AllocError(t.dst, "is not a struct")
            # this Put constitutes a spill to the struct
            if t.dst in self.stack:
                sp, typ, size, filled, spilled = self.stack[t.dst]
                assert typ == dtyp, self.stack[t.dst]
                self.stack[t.dst] = sp, typ, size, filled, True
            struct = self.structs[dtyp.tag]
            offset = struct.offsets[t.tag]
            if t.src not in self.names:
                raise AllocError("Name not found", t.src)
            styp = self.names[t.src][1]
            size = self.sizeof(styp)
            # don't need to lock IX/IY as nothing ever chooses them
            if size == 1:
                r = self.fetch_src_byte(t.src)
                self.code.append(self.RTLIndirectWrite(t.dst, offset, r))
            elif size == 2:
                hl = self.register('HL')
                hl.lock() # can't use HL with IX/IY
                r = self.fetch_src_word(t.src) # but it might already be in HL
                hl.unlock()
                if r.name == 'HL': # in which case let's move it
                    r = self.exdehl(r)
                self.code.append(self.RTLIndirectWrite(t.dst, offset, r))
            else:
                raise NotImplementedError(size, t)
            if kill_p(t.src):
                self.kill(t.src)
            if kill_p(t.dst):
                self.kill(t.dst)
            return
        if isinstance(t, TAC.TACInit):
            offset = 0
            sym = t.dst
            root = sym
            if self.is_on_stack(t.src):
                # we're initialising it (in-memory), that constitutes a spill
                sp, typ, size, filled, spilled = self.stack[t.src]
                self.stack[t.src] = sp, typ, size, filled, True
            while not isinstance(sym, TAC.Identifier):
                if isinstance(sym, TAC.Member):
                    nxt = sym.struct
                    tag = sym.tag
                    styp = nxt.typ
                    if not isinstance(styp, AST.Struct):
                        raise AllocError(sym, "is not a struct in", t)
                    if styp.tag not in self.structs:
                        raise AllocError(sym, "is incomplete struct in", t)
                    struct = self.structs[styp.tag]
                    if tag not in struct.offsets:
                        raise AllocError(sym, "references non-existent struct member in", t)
                    offset += struct.offsets[tag]
                    sym = nxt
                    continue
                raise NotImplementedError(sym)
            size = self.sizeof(root.typ)
            if size == 1:
                r = self.fetch_src_byte(t.src.name)
                self.code.append(self.RTLIndirectInit(sym.name, offset, r))
            elif size == 2:
                hl = self.register('HL')
                hl.lock() # can't use HL with IY
                r = self.fetch_src_word(t.src.name) # but it might already be in HL
                hl.unlock()
                if r.name == 'HL': # in which case let's move it
                    r = self.exdehl(r)
                self.code.append(self.RTLIndirectInit(sym.name, offset, r))
            else:
                raise NotImplementedError(size, t)
            if kill_p(t.src):
                self.kill(t.src)
            return
        raise NotImplementedError(t)
    def wraplabel(self, label):
        return '_%s_%s'%(self.name, label)
    def exdehl(self, follow):
        if follow and follow.size == 1:
            raise AllocError("exdehl following %s, size 1"%(follow,))
        de = self.register('DE')
        d, e = de.children
        hl = self.register('HL')
        h, l = hl.children
        locked = [r for r in (de, hl, d, e, h, l) if r.locked]
        if locked:
            raise AllocError("exdehl blocked by lock(s)", locked)
        deu = de.state
        hlu = hl.state
        self.code.append(self.RTLExchange(de, hl))
        hl.state = deu
        de.state = hlu
        if follow == de:
            return hl
        if follow == hl:
            return de
        if follow is None:
            return
        raise AllocError("exdehl with follow", follow)
    def clobber_flag_register(self, leave=None):
        if self.flags[0] not in (None, leave):
            # convert to byte, store in A
            # (if we were called by clobber_registers, A will then get spilled)
            a = self.register('A')
            if not a.available:
                if a.user == leave: # not sure if this can happen
                    raise AllocError("Clobber byte but must leave A", leave)
                self.spill(a)
            self.code.append(self.RTLMove(a, ByteLiteral(0))) # Warning!  This must not be optimised to 'XOR A' or we'll lose the flags!
            label = self.wraplabel(self.tac.genlabel())
            self.code.append(self.RTLCJump(label, self.flags[1].neg))
            self.code.append(self.RTLAdd(a, ByteLiteral(1)))
            self.code.append(self.RTLLabel(label))
            a.user = self.flags[0]
            a.dirty()
            self.flags = (None, None)
    def clobber_registers(self, leave=None):
        self.clobber_flag_register(leave=leave)
        for r in self.registers:
            if r.locked:
                raise AllocError("Clobbering locked register", r)
            if not r.available and r.user != leave:
                self.spill(r, leave=leave)
            if not r.user or r.user != leave:
                r.oldl = None
    @property
    def current_register_allocations(self):
        rv = {}
        for r in self.registers:
            if r.user:
                rv[str(r)] = r.user
            elif isinstance(r, SplittableRegister):
                for c in r.children:
                    if c.user:
                        rv[str(c)] = c.user
        return rv
    @property
    def void_function(self):
        if not isinstance(self.decl, AST.Function): # can't happen
            raise AllocError("Not in a function")
        return self.decl.ret.compat(AST.Void())
    def allocate_params(self):
        if not isinstance(self.decl, AST.Function): # can't happen
            raise AllocError(self.decl, "is not a Function")
        if self.wfunc_void:
            if len(self.decl.params) == 1 and self.decl.params[0].typ == AST.Void():
                self.warn("Warning: function '%s' takes single void argument.\n         Did you mean to declare it with no arguments?" % (self.name,))
        for p in self.decl.params:
            name = p.ident
            typ = p.typ
            size = self.sizeof(typ)
            self.stack[name] = [self.sp, typ, size, True, True]
            self.names[name] = (AST.Auto, typ)
            self.sp += size
            if self.sp > 128:
                raise AllocError("No room on stack for param", name, typ, size)
        self.caller_stack_size = self.sp
    def prepare_locals(self):
        # compute their sizes, but don't reserve stack space yet
        # after all, they might get optimised away
        for t in self.func:
            if isinstance(t, TAC.TACDeclare):
                name = t.name
                self.names[name] = (t.sc, t.typ)
                size = self.sizeof(t.typ)
                if t.sc.auto:
                    self.stack[name] = [None, t.typ, size, False, False]
                elif t.sc.static:
                    self.static[name] = (size, t.typ)
    def allocate_locals(self):
        for name,(sp, typ, size, filled, spilled) in self.stack.items():
            if filled and spilled and sp is None:
                self.stack[name] = [self.sp, typ, size, filled, spilled]
                self.sp += size
                if self.sp > 128:
                    raise AllocError("No room on stack for local", name, t.typ, size)
    def allocate_globals(self):
        for t in self.func:
            if isinstance(t, TAC.TACDeclare):
                name = t.name
                self.names[name] = (t.sc, t.typ)
                if isinstance(t.typ, AST.Function):
                    # Nothing to allocate here, it's just a prototype
                    continue
                size = self.sizeof(t.typ)
                if t.sc.auto:
                    self.stack[name] = [None, t.typ, size, True, True]
                elif t.sc.static:
                    self.static[name] = (size, t.typ)
            elif isinstance(t, TAC.TACStructDef):
                s = RTLStructDef(t.tag, t.defn)
                s.allocate(self)
                self.structs[t.tag] = s
            elif isinstance(t, TAC.TACEnumDef):
                e = RTLEnumDef(t.tag, t.typ, t.defn)
                e.allocate(self)
                self.enums[t.tag] = e
            elif isinstance(t, TAC.TACAssign):
                pass
            elif isinstance(t, TAC.TACAddress):
                pass
            else:
                raise AllocError("Unhandled", t)
    def allocate_registers(self):
        for t in self.func:
            try:
                self.tac_to_rtl(t)
            except:
                self.err("in TAC: %s"%(pprint.pformat(t),))
                self.err("with regs: %s"%(pprint.pformat(self.current_register_allocations),))
                raise
        if not self.code or not isinstance(self.code[-1], (self.RTLReturn, self.RTLJump)):
            if not self.void_function:
                raise AllocError("Control reached end of non-void function")
            # Spill all variables before function return
            # (if they're local or clean, we can optimise the spills away later)
            for r in self.registers:
                if not r.available:
                    self.spill(r)
            self.code.append(self.RTLReturn())
    def gather_initialisers(self):
        self.inits = {}
        for t in self.func:
            if isinstance(t, TAC.TACDeclare):
                if isinstance(t.typ, AST.Function):
                    continue
                if t.sc.static:
                    if t.name not in self.static: # can't happen
                        raise AllocError("Declared unknown static global", t)
                elif t.sc.auto:
                    if t.name not in self.stack: # can't happen
                        raise AllocError("Declared unknown global", t)
                self.inits[t.name] = self.tac.strings.get(t.name)
            elif isinstance(t, TAC.TACAssign):
                if t.dst not in self.inits: # can't happen
                    raise AllocError("Initialised undeclared global", t)
                if self.inits[t.dst] is not None: # also can't happen
                    raise AllocError("Initialised global", t, "but it was already initialised to", self.inits[t.dst])
                if t.dst in self.static:
                    size, typ = self.static[t.dst]
                elif t.dst in self.stack:
                    _, typ, size, _, _ = self.stack[t.dst]
                else: # can't happen?
                    raise AllocError("Initialised nonexistent global", t)
                if size == 1:
                    self.inits[t.dst] = self.fetch_src_byte(t.src)
                elif size == 2:
                    self.inits[t.dst] = self.fetch_src_word(t.src)
                else:
                    raise NotImplementedError(t)
            elif isinstance(t, TAC.TACStructDef):
                pass
            elif isinstance(t, TAC.TACEnumDef):
                pass
            elif isinstance(t, TAC.TACAddress):
                if t.src in self.static or t.src in self.stack:
                    self.inits[t.dst] = t
            else:
                raise NotImplementedError(t)
    def allocate(self):
        try:
            if self.name is None:
                self.allocate_globals()
                self.gather_initialisers()
            else:
                self.allocate_params()
                self.prepare_locals()
                self.allocate_registers()
                self.allocate_locals()
        except:
            self.err("In: %s %r"%(self.name, self.decl))
            raise
    def warn(self, *args):
        if self.werror:
            self.has_error = True
        print >>sys.stderr, ' '.join(map(str, args))
    def err(self, *args):
        self.has_error = True
        print >>sys.stderr, ' '.join(map(str, args))
    def debug(self):
        print "static:"
        pprint.pprint(self.static)
        print "stack:"
        pprint.pprint(self.stack)
        print "code:"
        pprint.pprint(self.code)
        print "structs:"
        for tag, struc in self.structs.items():
            print "  struct", tag
            for off, typ, memb, size in struc.members:
                print "    <+%02x> %r %s (%x)"%(off, typ, memb, size)
        print "enums:"
        for tag, enum in self.enums.items():
            print "  enum", enum.typ, tag
            for n, v in enum.values.items():
                print "    %s %d"%(n, v)

## Entry point

def alloc(tac, w_opts, debug=False):
    allocations = {}
    # Do file-scope first, to get struct and enum definitions
    if debug:
        print "Allocating globals"
    fs = Allocator(tac.functions[None], None, tac, w_opts)
    fs.allocate()
    if debug:
        fs.debug()
    allocations[None] = fs
    for name, func in tac.functions.items():
        if name is None: continue
        if debug:
            print "Allocating", name
        alloc = Allocator(func, name, tac, w_opts, outer=fs)
        alloc.structs = fs.structs
        alloc.allocate()
        if alloc.has_error:
            raise AllocError("Error emitted (see above)")
        if debug:
            alloc.debug()
        allocations[name] = alloc
    return allocations

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
    tac = tacifier.tacify(ast)
    tac.debug()
    assert tac.in_func is None, tac.in_func
    assert len(tac.scopes) == 1
    print
    allocations = alloc(tac, {'error': True}, debug=True)

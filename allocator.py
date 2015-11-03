#!/usr/bin/python

import sys, pprint
import parser, tacifier
LEX = parser.Lexer
PAR = parser.Parser
TAC = tacifier.TACifier

## Perform stack frame and register allocation on the TAC intermediate form
## to generate interim stack frame and RTL intermediate form

class AllocError(Exception): pass

builtin_sizes = {'bool':1, 'byte': 1, 'word': 2}

class Register(object):
    def __init__(self, name):
        self.name = name
        self.user = None
        self._lock = False
    @property
    def available(self):
        return not self.user
    def claim(self, user):
        if not self.available:
            raise AllocError("Attempted to claim %s, in use by %s"%(self, self.user))
        self.user = user
    def free(self):
        if self.locked:
            raise AllocError("Attempted to free %s, locked by %s"%(self, self.user))
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
    def free(self):
        if self.parent.user:
            raise AllocError("Attempted to free %s, in use by parent %s"%(self, self.parent))
        super(ByteRegister, self).free()
    @property
    def partner(self):
        return [c for c in self.parent.children if c != self][0]
    @property
    def available(self):
        return not (self.user or self.parent.user)
    @property
    def locked(self):
        return self._lock or self.parent._lock
class SplittableRegister(WordRegister):
    def __init__(self, name):
        super(SplittableRegister, self).__init__(name)
        self.children = [SplitByteRegister(n, self) for n in name]
        self.hi, self.lo = self.children
    def free(self):
        if any(c.user for c in self.children):
            raise AllocError("Attempted to free %s, in use by child %s"%(self, c))
        super(WordRegister, self).free()
    @property
    def available(self):
        return not (self.user or any(c.user for c in self.children))
    @property
    def locked(self):
        return self._lock or any(c._lock for c in self.children)
class Flag(object):
    def __init__(self, name):
        self.name = name
    def __repr__(self):
        return '#'+self.name

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
    class RTLIndirectWrite(RTLStatement):
        def __init__(self, dst, offset, src):
            self.dst = dst
            self.offset = offset
            self.src = src
        def __repr__(self):
            return 'RTLIndirectWrite(%s, %d, %s)'%(self.dst, self.offset, self.src)
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
    def __init__(self, func, name, tac):
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
        self.sc = sc or LEX.Auto("auto")
        self.decl = decl
        self.names = dict((name, (LEX.Extern("extern"), typ)) for name, (sc, typ) in globs.items())
        self.stack = {}
        self.sp = 0
        self.static = {}
        self.registers = [ByteRegister('A'),
                          SplittableRegister('BC'), SplittableRegister('DE'), SplittableRegister('HL'),
                          WordRegister('IX'), WordRegister('IY')]
        self.general_byte_registers = [self.register(n) for n in 'BCDEHL']
        self.general_word_registers = self.registers[1:4]
        self.all_byte_registers = [self.registers[0]] + self.general_byte_registers
        self.flags = None # (symbol (of bool type) currently stored in flags, flag it's stored in)
        self.code = []
    def register(self, name):
        for r in self.registers:
            if r.name == name: return r
            if isinstance(r, SplittableRegister):
                for c in r.children:
                    if c.name == name: return c
        raise AllocError("No such register", name)
    def sizeof(self, typ):
        if isinstance(typ, PAR.ValueOfType):
            if typ.typ in builtin_sizes:
                return builtin_sizes[typ.typ]
            raise AllocError("Unrecognised value type", typ)
        if isinstance(typ, PAR.Pointer):
            return 2
        if isinstance(typ, PAR.Array):
            esiz = self.sizeof(typ.pointee)
            return esiz * typ.n
        raise NotImplementedError("sizeof", typ)
    def is_on_stack(self, name):
        return name in self.stack
    def spill(self, r):
        if r.user:
            name = r.user
            if isinstance(name, (PAR.Literal, PAR.LongLiteral)):
                r.user = None # nothing to spill
                return
            assert name in self.names
            self.code.append(self.RTLSpill(r, name))
            r.free()
        elif isinstance(r, SplittableRegister):
            for c in r.children:
                if c.user:
                    self.spill(c)
        elif isinstance(r, SplitByteRegister):
            self.spill(r.parent)
        else:
            raise AllocError("Spilling empty register", r)
    def fill(self, r, name):
        assert name in self.names or isinstance(name, (PAR.Literal, PAR.LongLiteral))
        if r.user == name: # Nothing to do; we're already filled
            return
        assert r.available, (r, r.user, name)
        self.code.append(self.RTLFill(r, name))
        r.claim(name)
    def choose_byte_register(self, spill=True):
        # prefer BCDEHL (prefer a reg whose partner is in use), then A, then spill from BCDEHL
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
        raise NotImplementedError("choose spill")
    def choose_word_register(self, spill=True):
        # implicitly prefers BC > DE > HL
        for r in self.general_word_registers:
            if r.available:
                return r
        if not spill: return
        for r in self.general_word_registers:
            if not r.locked:
                self.spill(r)
                return r
        raise NotImplementedError("Can't spill, all locked")
    def fetch_src_byte(self, src):
        if isinstance(src, PAR.Literal):
            return src
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
                reg = self.choose_byte_register()
            else: # LD A,(nn)
                reg = self.free_a(src)
            self.fill(reg, src)
        return reg
    def fetch_src_word(self, src):
        if isinstance(src, PAR.LongLiteral):
            return src
        if isinstance(src, PAR.Literal):
            return PAR.LongLiteral(src.value)
        if src not in self.names:
            raise AllocError("Name not found", src)
        sc, typ = self.names[src]
        if isinstance(typ, PAR.Array):
            typ = PAR.Pointer(typ.pointee)
        size = self.sizeof(typ)
        if size != 2:
            raise AllocError("Wrong size:", src, "is", typ, "of size", size)
        # is it already in a register?
        reg = self.reg_find_word(src)
        if reg is None:
            # no; we'll have to load it into one
            if self.is_on_stack(src):
                reg = self.choose_word_register()
            else: # have to go via LD HL,(nn)
                reg = self.free_hl(src)
            self.fill(reg, src)
        return reg
    def reg_find_byte(self, name):
        assert name in self.names or isinstance(name, PAR.Literal)
        for r in self.all_byte_registers:
            if r.user == name:
                return r
        return
    def reg_find_word(self, name):
        assert name in self.names or isinstance(name, PAR.LongLiteral)
        for r in self.registers:
            if r.user == name:
                return r
        return
    def free_a(self, name):
        a = self.register('A')
        if a.user != name:
            if not a.available:
                move = self.choose_byte_register(False)
                if move:
                    move.claim(a.user)
                    self.code.append(self.RTLMove(move, a))
                    a.free()
                else:
                    self.spill(a)
        return a
    def free_hl(self, name):
        hl = self.register('HL')
        if hl.user != name:
            if not hl.available:
                move = self.choose_word_register(False)
                if move:
                    move.claim(hl.user)
                    self.code.append(self.RTLMove(move, hl))
                    hl.free()
                else:
                    self.spill(hl)
        return hl
    def load_byte_into_a(self, name):
        a = self.register('A')
        if a.user != name:
            if not a.available:
                move = self.choose_byte_register(False)
                if move:
                    move.claim(a.user)
                    self.code.append(self.RTLMove(move, a))
                    a.free()
                else:
                    self.spill(a)
            r = self.reg_find_byte(name)
            if r:
                a.claim(r.user)
                self.code.append(self.RTLMove(a, r))
                r.free()
            else:
                self.fill(a, name)
        return a
    def load_word_into_hl(self, name):
        hl = self.register('HL')
        if hl.user != name:
            if not hl.available: # don't bother trying to move, just spill it
                self.spill(hl)
            r = self.reg_find_word(name)
            if r: # move it to HL
                hl.claim(r.user)
                self.code.append(self.RTLMove(hl, r))
                r.free()
            else:
                self.fill(hl, name)
        return hl
    def tac_to_rtl(self, t):
        if isinstance(t, TAC.TACDeclare): return
        if isinstance(t, TAC.TACAssign):
            if t.dst not in self.names:
                raise AllocError("Name not found", t.dst)
            sc, typ = self.names[t.dst]
            size = self.sizeof(typ)
            if size == 1:
                s = self.fetch_src_byte(t.src)
                r = self.reg_find_byte(t.dst)
                if r is None: # just rename it
                    self.spill(s)
                    s.claim(t.dst)
                    return
                self.code.append(self.RTLMove(r, s))
                return
            elif size == 2:
                s = self.fetch_src_word(t.src)
                r = self.reg_find_word(t.dst)
                if r is None: # just rename it
                    self.spill(s)
                    s.claim(t.dst)
                    return
                self.code.append(self.RTLMove(r, s))
                return
            else:
                raise TACError("Tried to move an aggregate, size = %d"%(size,))
        if isinstance(t, TAC.TACAddress):
            if self.is_on_stack(t.src):
                raise NotImplementedError(t)
            else:
                # it's static
                r = self.reg_find_word(t.dst)
                if r is None:
                    r = self.choose_word_register()
                self.code.append(self.RTLMove(r, t.src))
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
                self.code.append(self.RTLAdd(a, r))
                a.unlock()
                return
            elif size == 2: # dst has to be in HL, src has to be in a register (even if literal).  EXCEPT if src is +/- 1, in which case we can INC/DEC
                if isinstance(t.src, (PAR.Literal, PAR.LongLiteral)):
                    if t.src.value in [1, -1]:
                        r = self.fetch_src_word(t.dst)
                        self.code.append(self.RTLAdd(r, t.src))
                        return
                    hl = self.load_word_into_hl(t.dst)
                    hl.lock()
                    r = self.choose_word_register()
                    self.fill(r, t.src)
                    self.code.append(self.RTLAdd(hl, r))
                    hl.unlock()
                    return
                hl = self.load_word_into_hl(t.dst)
                hl.lock()
                r = self.fetch_src_word(t.src)
                self.code.append(self.RTLAdd(hl, r))
                hl.unlock()
                return
            else:
                raise TACError("Tried to add to an aggregate, size = %d"%(size,))
        if isinstance(t, TAC.TACReturn):
            if t.src is not None: # else return type is void and there's nothing to return
                if isinstance(t.src, PAR.Literal):
                    typ = PAR.ValueOfType('byte')
                elif isinstance(t.src, PAR.LongLiteral):
                    typ = PAR.ValueOfType('word')
                else:
                    if t.src not in self.names:
                        raise AllocError("Name not found", t.src)
                    _, typ = self.names[t.src]
                size = self.sizeof(typ)
                if size == 1: # return in A
                    # No point trying to avoid spills, we're about to return
                    a = self.register('A')
                    if a.user != t.src:
                        if not a.available:
                            self.spill(a)
                        r = self.reg_find_byte(t.src)
                        if r:
                            a.claim(r.user)
                            self.code.append(self.RTLMove(a, r))
                            r.free()
                        else:
                            self.fill(a, t.src)
                else:
                    raise NotImplementedError(size)
            # Spill all variables before function return
            # (if they're local or clean, we can optimise the spills away later)
            for r in self.registers:
                if not r.available:
                    self.spill(r)
            self.code.append(self.RTLReturn())
            return
        if isinstance(t, TAC.TACDeref):
            if t.dst not in self.names:
                raise AllocError("Name not found", t.dst)
            dsc, dtyp = self.names[t.dst]
            if t.src not in self.names:
                raise AllocError("Name not found", t.src)
            ssc, styp = self.names[t.src]
            if not isinstance(styp, PAR.Pointer):
                raise AllocError("Not of pointer type", t.src, styp)
            p = self.reg_find_word(t.src)
            size = self.sizeof(dtyp)
            if size == 1:
                r = self.reg_find_byte(t.dst)
                if (p == self.register('HL')):
                    # LD r,(HL)
                    if not r:
                        p.lock() # don't try to use H or L
                        r = self.choose_byte_register()
                        r.claim(t.dst) # no need to fill, as we're assigning to it
                        p.unlock()
                elif (r == self.register('A')):
                    # LD A,(pp)
                    raise NotImplementedError(r, p)
                elif r and r.name not in 'HL':
                    # LD r,(HL)
                    raise NotImplementedError(r, p)
                elif p:
                    # LD A,(pp)
                    raise NotImplementedError(r, p)
                elif self.register('HL').available: # r must be None (else r.name in 'HL', contra)
                    # LD r,(HL)
                    p = self.register('HL')
                    self.fill(p, t.src)
                    p.lock() # don't try to use H or L
                    r = self.choose_byte_register()
                    r.claim(t.dst) # no need to fill, as we're assigning to it
                    p.unlock()
                elif self.register('A').available and not r:
                    # LD A,(pp)
                    r = self.register('A')
                    r.claim(t.dst) # no need to fill, as we're assigning to it
                    p = self.choose_word_register()
                    self.fill(p, t.src)
                else:
                    raise NotImplementedError(r, p)
                self.code.append(self.RTLDeref(r, p))
                return
            else:
                r = self.reg_find_word(t.dst)
                raise NotImplementedError(size)
        if isinstance(t, TAC.TACWrite):
            if t.dst not in self.names:
                raise AllocError("Name not found", t.dst)
            dsc, dtyp = self.names[t.dst]
            if t.src not in self.names:
                raise AllocError("Name not found", t.src)
            ssc, styp = self.names[t.src]
            if not isinstance(dtyp, PAR.Pointer):
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
                    raise NotImplementedError(r, p)
                elif r and r.name not in 'HL':
                    r.lock()
                    # LD (HL),r
                    if p:
                        # PUSH/POP to swap it with HL
                        raise NotImplementedError(r, p)
                    else:
                        p = self.free_hl(t.dst)
                        self.fill(p, t.dst)
                    r.unlock()
                elif p:
                    # LD (pp),A
                    raise NotImplementedError(r, p)
                elif self.register('HL').available: # r must be None (else r.name in 'HL', contra)
                    # LD r,(HL)
                    p = self.register('HL')
                    self.fill(p, t.dst)
                    p.lock() # don't try to use H or L
                    r = self.fetch_src_byte(t.src)
                    p.unlock()
                elif self.register('A').available and not r:
                    # LD (pp),A
                    r = self.free_a()
                    self.fill(r, t.src)
                    p = self.choose_word_register()
                    self.fill(p, t.src)
                else:
                    raise NotImplementedError(r, p)
                self.code.append(self.RTLWrite(p, r))
                return
            else:
                r = self.reg_find_word(t.src)
                raise NotImplementedError(size)
        if isinstance(t, TAC.TACCall):
            # CALLING SEQUENCE
            # IX := IY
            # IX += caller-stack-size
            # build callee initial stack frame through (IX+d)
            # spill everything
            # PUSH IY
            # IY := IX
            # CALL
            # POP IY
            ix = self.register('IX')
            iy = self.register('IY')
            self.code.append(self.RTLMove(ix, iy))
            css = self.choose_word_register() # caller stack size
            if css.name == 'HL': # that's no good to us, we need something we can add to IX
                css = self.exdehl(css)
            self.fill(css, PAR.Literal(self.sp + 1))
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
            self.code.append(self.RTLIndirectWrite(ix, -1, PAR.Literal(csp)))
            # Spill all variables before function call
            # (if they're clean, we can optimise the spills away later)
            for r in self.registers:
                if not r.available:
                    self.spill(r)
            self.code.append(self.RTLPush(iy))
            self.code.append(self.RTLMove(iy, ix))
            if self.is_on_stack(t.func.name):
                raise NotImplementedError(t)
            else:
                self.code.append(self.RTLCall(t.func.name))
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
            if size == 1: # dst has to be in A
                r = self.fetch_src_byte(t.right)
                r.lock()
                if r.name == 'A': # have to shunt it out of the way
                    s = self.choose_byte_register()
                    self.code.append(self.RTLMove(s, r))
                    s.claim(r.user)
                    s.lock()
                    r.unlock()
                    r.free()
                    r = s
                a = self.load_byte_into_a(t.left)
                r.unlock()
                if t.op == '==':
                    self.code.append(self.RTLCp(a, r))
                    self.code.append(self.RTLMove(a, PAR.Literal(0))) # Warning!  This must not be optimised to 'XOR A' or we'll lose the flags!
                    label = self.tac.genlabel()
                    self.code.append(self.RTLCJump(label, Flag('Z')))
                    self.code.append(self.RTLAdd(a, PAR.Literal(1)))
                    self.code.append(self.RTLLabel(label))
                    a.user = t.dst
                    return
                raise NotImplementedError(t.op)
            raise NotImplementedError(size)
        if isinstance(t, TAC.TACLabel):
            self.clobber_registers()
            self.code.append(self.RTLLabel(self.wraplabel(t.name)))
            return
        if isinstance(t, TAC.TACIf):
            if t.cond not in self.names:
                raise AllocError("Name not found", t.cond)
            sc, typ = self.names[t.cond]
            size = self.sizeof(typ)
            # spill all registers
            self.clobber_registers()
            if size == 1: # cond has to be in A
                a = self.load_byte_into_a(t.cond)
                self.code.append(self.RTLAnd(a, a))
                self.code.append(self.RTLCJump(self.wraplabel(t.label), Flag('Z')))
                self.spill(a)
                return
            raise NotImplementedError(size)
        if isinstance(t, TAC.TACGoto):
            # spill all registers
            self.clobber_registers()
            self.code.append(self.RTLJump(self.wraplabel(t.label)))
            return
        raise NotImplementedError(t)
    def wraplabel(self, label):
        return LEX.Identifier('_%s_%s'%(self.name, label))
    def exdehl(self, follow):
        de = self.register('DE')
        d, e = de.children
        hl = self.register('HL')
        h, l = hl.children
        locked = [r for r in (de, hl, d, e, h, l) if r.locked]
        if locked:
            raise AllocError("exdehl blocked by lock(s)", locked)
        deu = (de.user, d.user, e.user)
        hlu = (hl.user, h.user, l.user)
        self.code.append(self.RTLExchange(de, hl))
        (hl.user, h.user, l.user) = deu
        (de.user, d.user, e.user) = hlu
        if follow == de:
            return hl
        if follow == hl:
            return de
        if follow is None:
            return
        raise AllocError("exdehl with follow", follow)
    def clobber_registers(self):
        for r in self.registers:
            if r.locked:
                raise AllocError("Clobbering locked register", r)
            if not r.available:
                self.spill(r)
        if self.flags:
            raise NotImplementedError("Spilling flags on clobber")
            self.flags = None
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
        if not isinstance(self.decl, PAR.FunctionDecl): # can't happen
            raise TACError("Not in a function")
        return self.decl.bound == PAR.ValueOfType("void")
    def allocate_params(self):
        if not isinstance(self.decl, PAR.FunctionDecl): # can't happen
            raise AllocError(self.decl, "is not a FunctionDecl")
        if not self.decl.arglist.args:
            raise AllocError(self.decl, "has no arglist")
        if len(self.decl.arglist.args) == 1 and self.decl.arglist.args[0][1] == PAR.ValueOfType("void"):
            pass # no arguments
        else:
            for nam,typ in self.decl.arglist.args:
                size = self.sizeof(typ)
                self.stack[nam] = (self.sp, typ, size)
                self.names[nam] = (LEX.Auto("auto"), typ)
                self.sp += size
                if self.sp > 127:
                    raise AllocError("No room on stack for param", nam, typ, size)
        self.caller_stack_size = self.sp
    def allocate_locals(self):
        for t in self.func:
            if isinstance(t, TAC.TACDeclare):
                name = t.name
                self.names[name] = (t.sc, t.typ)
                size = self.sizeof(t.typ)
                if isinstance(t.sc, LEX.Auto):
                    self.stack[name] = (self.sp, t.typ, size)
                    self.sp += size
                    if self.sp > 127:
                        raise AllocError("No room on stack for local", name, t.typ, size)
                elif isinstance(t.sc, LEX.Static):
                    self.static[name] = (size, t.typ)
                else:
                    raise TACError(t.sc)
    def allocate_globals(self):
        for t in self.func:
            if isinstance(t, TAC.TACDeclare):
                name = t.name
                self.names[name] = (t.sc, t.typ)
                size = self.sizeof(t.typ)
                if isinstance(t.sc, (LEX.Auto, LEX.Static)):
                    self.stack[name] = (None, t.typ, size)
                else:
                    raise TACError(t.sc)
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
                if t.name not in self.stack: # can't happen
                    raise AllocError("Declared unknown global", t)
                self.inits[t.name] = None
            elif isinstance(t, TAC.TACInitGlobal):
                if t.name not in self.inits: # can't happen
                    raise AllocError("Initialised undeclared global", t)
                if self.inits[t.name] is not None: # also can't happen
                    raise AllocError("Initialised global", t, "but it was already initialised to", self.inits[t.name])
                self.inits[t.name] = t.value
            else:
                raise NotImplementedError(t)
    def allocate(self):
        try:
            if self.name is None:
                self.allocate_globals()
                self.gather_initialisers()
            else:
                self.allocate_params()
                self.allocate_locals()
                self.allocate_registers()
        except:
            self.err("In: %s %r"%(self.name, self.decl))
            raise
    def err(self, text):
        print >>sys.stderr, text

## Entry point

def alloc(parse_tree, tac):
    allocations = {}
    for name, func in tac.functions.items():
        alloc = Allocator(func, name, tac)
        alloc.allocate()
        allocations[name] = alloc
    return allocations

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
    tac = tacifier.tacify(parse_tree)
    print "TAC functions:"
    pprint.pprint(tac.functions)
    assert tac.in_func is None, tac.in_func
    assert len(tac.scopes) == 1
    print
    allocations = {}
    for name, func in tac.functions.items():
        print "Allocating", name or "globals"
        alloc = Allocator(func, name, tac.scopes[0])
        alloc.allocate()
        allocations[name] = alloc

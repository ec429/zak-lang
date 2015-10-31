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
        self.user = user
    def free(self):
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
class ByteRegister(Register):
    size = 1
class WordRegister(Register):
    size = 2
class SplitByteRegister(ByteRegister):
    def __init__(self, name, parent):
        super(SplitByteRegister, self).__init__(name)
        self.parent = parent
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
    @property
    def available(self):
        return not (self.user or any(c.user for c in self.children))
    @property
    def locked(self):
        return self._lock or any(c._lock for c in self.children)

class Allocator(object):
    class RTLStatement(object):
        def __repr__(self):
            return '%s()'%(self.__class__.__name__,)
    class RTLReturn(RTLStatement): pass
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
    class RTLDeref(RTLStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def __repr__(self):
            return 'RTLDeref(%s, %s)'%(self.dst, self.src)
    class RTLAdd(RTLStatement):
        def __init__(self, dst, src):
            self.dst = dst
            self.src = src
        def __repr__(self):
            return 'RTLAdd(%s, %s)'%(self.dst, self.src)
    def __init__(self, func, name, globs):
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
        raise NotImplementedError("sizeof", typ)
    def allocate_params(self):
        if self.decl is None: return
        if not isinstance(self.decl, PAR.FunctionDecl): # can't happen
            raise AllocError(self.decl, "is not a FunctionDecl")
        for nam,typ in self.decl.arglist.args:
            size = self.sizeof(typ)
            self.stack[nam] = (self.sp, typ, size)
            self.names[nam] = (LEX.Auto("auto"), typ)
            self.sp += size
            if self.sp > 255: # we know that _all_ these will have to have real stack slots, unlike locals
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
                else:
                    raise NotImplementedError(t.sc)
    def spill(self, r):
        if r.user:
            name = r.user
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
        assert name in self.names
        assert r.available
        self.code.append(self.RTLFill(r, name))
        r.user = name
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
        # implicitly prefers BC/DE to HL
        for r in self.general_word_registers:
            if r.available:
                return r
        if not spill: return
        raise NotImplementedError("choose spill")
    def fetch_src_byte(self, src):
        # is it already in a register?
        reg = self.reg_find_byte(src)
        if reg is None:
            # no; we'll have to load it into one
            reg = self.choose_byte_register()
            self.fill(reg, src)
        return reg
    def reg_find_byte(self, name):
        assert name in self.names
        for r in self.all_byte_registers:
            if r.user == name:
                return r
        return
    def reg_find_word(self, name):
        assert name in self.names
        for r in self.registers:
            if r.user == name:
                return r
        return
    def load_byte_into_a(self, name):
        a = self.register('A')
        if a.user != name:
            if not a.available:
                move = self.choose_byte_register(False)
                if move:
                    move.user = a.user
                    self.code.append(self.RTLMove(move, a))
                    a.free()
                else:
                    self.spill(a)
            r = self.reg_find_byte(name)
            if r:
                a.user = r.user
                self.code.append(self.RTLMove(a, r))
                r.free()
            else:
                self.fill(a, name)
        return a
    def tac_to_rtl(self, t):
        if isinstance(t, TAC.TACDeclare): return
        if isinstance(t, TAC.TACAdd):
            if t.dst not in self.names:
                raise AllocError("Name not found", t.dst)
            sc, typ = self.names[t.dst]
            size = self.sizeof(typ)
            if size == 1: # dst has to be in A
                a = self.load_byte_into_a(t.dst)
                a.lock()
                r = self.fetch_src_byte(t.src)
                a.unlock()
                self.code.append(self.RTLAdd(a, r))
                return
            else:
                raise NotImplementedError(size)
        if isinstance(t, TAC.TACReturn):
            if t.src not in self.names:
                raise AllocError("Name not found", t.src)
            sc, typ = self.names[t.src]
            size = self.sizeof(typ)
            if size == 1: # return in A
                # No point trying to avoid spills, we're about to return
                a = self.register('A')
                if a.user != t.src:
                    if not a.available:
                        self.spill(a)
                    r = self.reg_find_byte(t.src)
                    if r:
                        a.user = r.user
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
                        p.unlock()
                        r.user = t.dst # no need to fill, as we're assigning to it
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
                    p.unlock()
                    r.user = t.dst # no need to fill, as we're assigning to it
                elif self.register('A').available and not r:
                    # LD A,(pp)
                    r = self.register('A')
                    r.user = t.dst # no need to fill, as we're assigning to it
                    p = self.choose_word_register()
                    self.fill(p, t.src)
                else:
                    raise NotImplementedError(r, p)
                self.code.append(self.RTLDeref(r, p))
                return
            else:
                r = self.reg_find_word(t.dst)
                raise NotImplementedError(size)
        raise NotImplementedError(t)
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
    def allocate_registers(self):
        for t in self.func:
            try:
                self.tac_to_rtl(t)
            except:
                print "in TAC:", pprint.pformat(t)
                print "with regs:", pprint.pformat(self.current_register_allocations)
                raise
    def allocate(self):
        self.allocate_params()
        self.allocate_locals()
        print "Interim Stack:"
        print self.stack
        print "Stack size:", self.sp
        if self.decl is not None:
            try:
                self.allocate_registers()
            finally:
                print "RTL output:"
                pprint.pprint(self.code)

## Entry point

def alloc(parse_tree, tac):
    allocations = {}
    for name, func in tac.functions.items():
        alloc = Allocator(func, name, tac.scopes[0])
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

#!/usr/bin/python

import sys, pprint, string
import ast_build as AST, tacifier, allocator
TAC = tacifier.TACifier
REG = allocator.Register
SRG = allocator.SplittableRegister
LIT = allocator.Literal
RTL = allocator.Allocator
Flag = allocator.Flag

class GenError(Exception): pass

class Generator(object):
    def __init__(self, rtl, name):
        self.rtl = rtl
        self.name = name
        self.text = []
        self.data = []
        self.bss = []
    def staticname(self, name):
        if isinstance(name, TAC.Gensym):
            return '__gensym_%d'%(name.n,)
        return name
    def print_stats(self):
        print "Lines: %d bss, %d data, %d text"%(len(self.bss), len(self.data), len(self.text))

## Generate Z80 assembly code from the stack & RTL

class FunctionGenerator(Generator):
    def extend_stack_frame(self):
        if self.rtl.sp > 127:
            raise GenError("Stack too big (%d bytes, max 127)"%(self.rtl.sp,))
        if self.rtl.sp > self.rtl.caller_stack_size:
            self.text.append("\tLD (IY-1),%d"%(self.rtl.sp,))
            # TODO optional stack-frame zeroing (in case of uninitialised variables)?
        elif self.rtl.sp < self.rtl.caller_stack_size: # what the heck?
            raise GenError("Stack shrunk (not allowed)")
    def generate_op(self, op):
        if isinstance(op, RTL.RTLReturn):
            self.text.append("\tRET")
        elif isinstance(op, RTL.RTLFill):
            assert isinstance(op.reg, REG), op
            if self.rtl.is_on_stack(op.name):
                offset, typ, size, filled, spilled = self.rtl.stack[op.name]
                if offset is None: # technically this might be able to happen, but I don't see how
                    raise GenError("Fill reg %s with non-backed %s"%(op.reg, op.name))
                if size != op.reg.size:
                    raise GenError("Fill reg %s (%d) with %s (%d)"%(op.reg, op.reg.size, op.name, size))
                if size == 1:
                    self.text.append("\tLD %s,(IY+%d)"%(op.reg, offset))
                elif size == 2:
                    self.text.append("\tLD %s,(IY+%d)"%(op.reg.lo, offset))
                    self.text.append("\tLD %s,(IY+%d)"%(op.reg.hi, offset+1))
                else: # can't happen
                    raise GenError(size)
            elif isinstance(op.name, LIT):
                # if it's a word register, it auto-promotes the literal
                assert op.reg.size >= op.name.size
                self.text.append("\tLD %s,%d"%(op.reg, op.name.value))
            else:
                if op.reg.name == 'A':
                    name = self.staticname(op.name)
                    self.text.append("\tLD A,(%s)"%(op.name,))
                elif op.reg.name == 'HL':
                    name = self.staticname(op.name)
                    self.text.append("\tLD HL,(%s)"%(op.name,))
                else:
                    raise GenError("Fill", op.reg, "with static", op.name)
        elif isinstance(op, RTL.RTLSpill):
            assert isinstance(op.reg, REG), op
            if self.rtl.is_on_stack(op.name):
                offset, typ, size, filled, spilled = self.rtl.stack[op.name]
                if offset is None:
                    if filled: # can't happen
                        raise GenError("Spill reg %s to non-backed %s"%(op.reg, op.name))
                    # nothing to do, it's not backed
                else:
                    if size != op.reg.size:
                        raise GenError("Spill reg %s (%d) to %s (%d)"%(op.reg, op.reg.size, op.name, size))
                    if size == 1:
                        self.text.append("\tLD (IY+%d),%s"%(offset, op.reg))
                    elif size == 2:
                        self.text.append("\tLD (IY+%d),%s"%(offset, op.reg.lo))
                        self.text.append("\tLD (IY+%d),%s"%(offset+1, op.reg.hi))
                    else: # can't happen
                        raise GenError(size)
            else:
                if op.reg.name == 'A':
                    raise NotImplementedError("Spill A to static %s"%(op.name,))
                else:
                    self.text.append("\tPUSH AF")
                    self.text.append("\tLD A,%s"%(op.reg,))
                    self.text.append("\tLD (%s),A"%(op.name,))
                    self.text.append("\tPOP AF")
        elif isinstance(op, RTL.RTLDeref):
            assert isinstance(op.dst, REG), op
            assert isinstance(op.src, REG), op
            assert op.src.size == 2, op
            if op.dst.size == 1:
                self.text.append("\tLD %s,(%s)"%(op.dst, op.src))
            elif op.dst.size == 2:
                self.text.append("\tLD %s,(%s)"%(op.dst.lo, op.src))
                self.text.append("\tINC %s"%(op.src,))
                self.text.append("\tLD %s,(%s)"%(op.dst.hi, op.src))
                self.text.append("\tDEC %s"%(op.src,))
            else:
                raise NotImplementedError(op.dst.size)
        elif isinstance(op, RTL.RTLWrite):
            assert isinstance(op.dst, REG), op
            assert isinstance(op.src, REG), op
            assert op.dst.size == 2, op
            if op.src.size == 1:
                self.text.append("\tLD (%s),%s"%(op.dst, op.src))
            else:
                raise NotImplementedError(op.src.size)
        elif isinstance(op, RTL.RTLIndirectRead):
            assert isinstance(op.src, REG), op
            assert isinstance(op.dst, REG), op
            assert op.src.size == 2, op
            if op.dst.size == 1:
                self.text.append("\tLD %s,(%s%+d)"%(op.dst, op.src, op.offset))
            elif op.dst.size == 2:
                self.text.append("\tLD %s,(%s%+d)"%(op.dst.lo, op.src, op.offset))
                self.text.append("\tLD %s,(%s%+d)"%(op.dst.hi, op.src, op.offset + 1))
            else:
                raise GenError(op.dst.size)
        elif isinstance(op, RTL.RTLIndirectWrite):
            assert isinstance(op.dst, REG), op
            assert op.dst.size == 2, op
            if isinstance(op.src, REG):
                if op.src.size == 1:
                    self.text.append("\tLD (%s%+d),%s"%(op.dst, op.offset, op.src))
                elif op.src.size == 2:
                    self.text.append("\tLD (%s%+d),%s"%(op.dst, op.offset, op.src.lo))
                    self.text.append("\tLD (%s%+d),%s"%(op.dst, op.offset + 1, op.src.hi))
                else:
                    raise GenError(op.src.size)
            elif isinstance(op.src, LIT):
                self.text.append("\tLD (%s%+d),%s"%(op.dst, op.offset, op.src.value))
            else:
                raise GenError(op)
        elif isinstance(op, RTL.RTLMove):
            assert isinstance(op.dst, REG), op
            if isinstance(op.src, REG):
                assert op.dst.size >= op.src.size, op
                if op.dst.size == 1:
                    self.text.append("\tLD %s,%s"%(op.dst, op.src))
                elif op.dst.size == 2:
                    if op.src.size == 1:
                        self.text.append("\tLD %s,0"%(op.dst.hi,))
                        self.text.append("\tLD %s,%s"%(op.dst.lo, op.src))
                    elif isinstance(op.dst, SRG) and isinstance(op.src, SRG):
                        self.text.append("\tLD %s,%s"%(op.dst.hi, op.src.hi))
                        self.text.append("\tLD %s,%s"%(op.dst.lo, op.src.lo))
                    else:
                        self.text.append("\tPUSH %s"%(op.src,))
                        self.text.append("\tPOP %s"%(op.dst,))
                else:
                    raise GenError(op.dst.size)
            elif isinstance(op.src, (TAC.Gensym, str)):
                # we assume it's a global symbol, and thus its name exists
                self.text.append("\tLD %s,%s"%(op.dst, self.staticname(op.src)))
            elif isinstance(op.src, LIT):
                assert op.dst.size <= op.src.size, op
                self.text.append("\tLD %s,%d"%(op.dst, op.src.value))
            else:
                raise NotImplementedError(op.src)
        elif isinstance(op, RTL.RTLExchange):
            assert isinstance(op.dst, REG), op
            assert isinstance(op.src, REG), op
            self.text.append("\tEX %s,%s"%(op.dst, op.src))
        elif isinstance(op, RTL.RTLAdd):
            assert isinstance(op.dst, REG), op
            if isinstance(op.src, REG):
                if op.dst.name == 'A': # 8-bit add
                    if op.src.size != 1: # should never happen
                        raise GenError("Add A with %s (%d)"%(op.src, op.src.size))
                    self.text.append("\tADD %s,%s"%(op.dst,op.src))
                elif op.dst.name in ['HL', 'IX', 'IY']: # 16-bit add
                    if op.src.size != 2: # should never happen
                        raise GenError("Add %s with %s (%d)"%(op.dst, op.src, op.src.size))
                    self.text.append("\tADD %s,%s"%(op.dst, op.src))
                else:
                    raise NotImplementedError(op)
            elif isinstance(op.src, LIT):
                assert op.dst.size == op.src.size, op
                if op.src.value == 1:
                    self.text.append("\tINC %s"%(op.dst,))
                else:
                    raise NotImplementedError(op)
            else:
                raise NotImplementedError(op)
        elif isinstance(op, RTL.RTLCp):
            assert isinstance(op.dst, REG), op
            if op.dst.name == 'A': # 8-bit compare
                if op.src.size != 1: # should never happen
                    raise GenError("Cp A with %s (%d)"%(op.src, op.src.size))
                assert isinstance(op.src, (REG,LIT)), op
                self.text.append("\tCP %s"%(op.src,))
            else:
                raise NotImplementedError(op)
        elif isinstance(op, RTL.RTLAnd):
            assert isinstance(op.dst, REG), op
            if isinstance(op.src, REG):
                if op.dst.name == 'A': # 8-bit and
                    if op.src.size != 1: # should never happen
                        raise GenError("And A with %s (%d)"%(op.src, op.src.size))
                    self.text.append("\tAND %s"%(op.src,))
            else:
                raise NotImplementedError(op)
        elif isinstance(op, RTL.RTLPush):
            assert isinstance(op.src, REG), op
            self.text.append("\tPUSH %s"%(op.src,))
        elif isinstance(op, RTL.RTLPop):
            assert isinstance(op.dst, REG), op
            self.text.append("\tPOP %s"%(op.dst,))
        elif isinstance(op, RTL.RTLLabel):
            assert isinstance(op.name, str), op
            self.text.append("%s:"%(op.name,))
        elif isinstance(op, RTL.RTLCall):
            assert isinstance(op.addr, str), op
            self.text.append("\tCALL %s"%(op.addr,))
        elif isinstance(op, RTL.RTLJump): # TODO notice when we need to use long JP (but how?)
            assert isinstance(op.label, str), op
            self.text.append("\tJR %s"%(op.label))
        elif isinstance(op, RTL.RTLCJump): # TODO notice when we need to use long JP (but how?)
            assert isinstance(op.label, str), op
            assert isinstance(op.flag, Flag)
            self.text.append("\tJR %s,%s"%(op.flag.name, op.label))
        else:
            raise NotImplementedError(op)
    def generate(self):
        for name, (size, typ) in self.rtl.static.items():
            if name in self.rtl.tac.strings:
                self.data.append("%s: .asciz \"%s\""%(self.staticname(name), self.escape_string(self.rtl.tac.strings[name])))
            else:
                self.err(self.rtl.tac.strings)
                raise NotImplementedError(name, size, typ)
        self.text.append("")
        if self.rtl.sc.auto:
            self.text.append(".globl %s ; %s"%(self.name, self.rtl.decl))
        elif self.rtl.sc.static:
            self.text.append("; (static) %s"%(self.rtl.decl,))
        else:
            raise GenError("Unexplained storage class", self.rtl.sc)
        self.text.append("; Stack:")
        stack = dict((offset, name) for (name,(offset, typ, size, filled, spilled)) in self.rtl.stack.items())
        for offset, name in stack.items():
            if offset is not None:
                self.text.append("; %d: %s"%(offset, name))
        self.text.append("%s:"%(self.name,))
        self.extend_stack_frame()
        for op in self.rtl.code:
            try:
                self.generate_op(op)
            except:
                self.err("In func: %s %s"%(self.name, self.rtl.decl))
                self.err("In op: %r"%(op,))
                raise
    def escape_string(self, s):
        out = []
        for c in s:
            if c == '"':
                out.append('\\"')
            elif c in string.printable:
                out.append(c)
            else:
                out.append('\\%03o'%(ord(c),))
        return ''.join(out)
    def err(self, text):
        print >>sys.stderr, text

## Generate assembler directives for the global variables

class GlobalGenerator(Generator):
    def generate(self):
        things = {}
        for name, (_, typ, size, filled, spilled) in self.rtl.stack.items():
            if not filled and spilled: # can't happen
                raise GenError("Global is not memory-backed", name)
            if name not in self.rtl.inits: # can't happen
                raise GenError("Undeclared global", name)
            things[name] = (size, typ)
        things.update(self.rtl.static)
        for name, (size, typ) in things.items():
            init = self.rtl.inits[name]
            name = self.staticname(name)
            if init is None:
                self.bss.append(".globl %s ; %s"%(name,typ))
                self.bss.append("%s: .skip %d"%(name, size))
            else:
                self.data.append(".globl %s ; %s"%(name,typ))
                self.data.append("%s:"%(name,))
                if isinstance(init, LIT):
                    if not typ.compat(init.typ):
                        raise GenError("Literal", init, "doesn't match type", typ, "of", name)
                    if size == 1:
                        self.data.append("\t.byte %d"%(init.value,))
                    elif size == 2:
                        self.data.append("\t.word %d"%(init.value,))
                    else:
                        raise GenError("Bad size", size, "for name", name, "with literal initialiser", init)
                elif isinstance(init, TAC.TACAddress):
                    self.data.append("\t.word %s"%(self.staticname(init.src),))
                elif isinstance(init, str):
                    # Don't trust .asciz, it can't cope with special chars like \n
                    self.data.append("\t; %r"%(init,))
                    self.data.append('\t.byte %s'%(', '.join(('%d'%(ord(ch),) for ch in init))))
                    self.data.append('\t.byte 0')
                else:
                    raise NotImplementedError(init)

## Entry point

def generate(allocations):
    generated = {}
    for name, rtl in allocations.items():
        if name is None:
            gen = GlobalGenerator(rtl, name)
            gen.generate()
            generated[name] = gen
        else:
            gen = FunctionGenerator(rtl, name)
            gen.generate()
            generated[name] = gen
    return generated

def combine(generated):
    bss = []
    data = []
    text = []
    for gen in generated.values():
        bss.extend(gen.bss)
        data.extend(gen.data)
        text.extend(gen.text)
    return bss, data, text

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
    assert tac.in_func is None, tac.in_func
    assert len(tac.scopes) == 1
    allocations = allocator.alloc(tac, debug=True)
    print
    generated = {}
    for name, rtl in allocations.items():
        if name is None:
            print "Generating global variables"
            gen = GlobalGenerator(rtl, name)
            gen.generate()
            gen.print_stats()
            generated[name] = gen
        else:
            print "Generating code for", name
            gen = FunctionGenerator(rtl, name)
            gen.generate()
            gen.print_stats()
            generated[name] = gen
    bss = []
    data = []
    text = []
    for gen in generated.values():
        bss.extend(gen.bss)
        data.extend(gen.data)
        text.extend(gen.text)
    print "==ASSEMBLY OUTPUT BEGINS HERE=="
    if bss:
        print
        print ".bss"
        for line in bss:
            print line
    if data:
        print
        print ".data"
        for line in data:
            print line
    if text:
        print
        print ".text"
        for line in text:
            print line

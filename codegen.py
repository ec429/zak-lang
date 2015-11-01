#!/usr/bin/python

import sys, pprint
import parser, tacifier, allocator
LEX = parser.Lexer
PAR = parser.Parser
TAC = tacifier.TACifier
REG = allocator.Register
RTL = allocator.Allocator

class GenError(Exception): pass

class Generator(object):
    def __init__(self, rtl, name):
        self.rtl = rtl
        self.name = name
        self.text = []
        self.data = []
        self.bss = []
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
                offset, typ, size = self.rtl.stack[op.name]
                if size != op.reg.size:
                    raise GenError("Fill reg %s (%d) with %s (%d)"%(op.reg, op.reg.size, op.name, size))
                if size == 1:
                    self.text.append("\tLD %s,(IY+%d)"%(op.reg, offset))
                elif size == 2:
                    self.text.append("\tLD %s,(IY+%d)"%(op.reg.lo, offset))
                    self.text.append("\tLD %s,(IY+%d)"%(op.reg.hi, offset+1))
                else: # can't happen
                    raise GenError(size)
            else:
                if op.reg.name == 'A':
                    raise NotImplementedError("Fill A with static %s"%(op.name,))
                else:
                    raise GenError("Fill", op.reg, "with static", op.name)
        elif isinstance(op, RTL.RTLSpill):
            assert isinstance(op.reg, REG), op
            if self.rtl.is_on_stack(op.name):
                offset, typ, size = self.rtl.stack[op.name]
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
                    raise GenError("Spill", op.reg, "to static", op.name)
        elif isinstance(op, RTL.RTLDeref):
            assert isinstance(op.dst, REG), op
            assert isinstance(op.src, REG), op
            assert op.src.size == 2, op
            if op.dst.size == 1:
                self.text.append("\tLD %s,(%s)"%(op.dst, op.src))
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
        elif isinstance(op, RTL.RTLMove):
            assert isinstance(op.dst, REG), op
            assert isinstance(op.src, REG), op
            assert op.dst.size == op.src.size, op
            if op.dst.size == 1:
                self.text.append("\tLD %s,%s"%(op.dst, op.src))
            else:
                raise NotImplementedError(size)
        elif isinstance(op, RTL.RTLAdd):
            assert isinstance(op.dst, REG), op
            assert isinstance(op.src, REG), op
            if op.dst.name == 'A': # 8-bit add
                if op.src.size != 1: # should never happen
                    raise GenError("Add A with %s (%d)"%(op.src, op.src.size))
                self.text.append("\tADD %s"%(op.src,))
        else:
            raise NotImplementedError(op)
    def generate(self):
        if not isinstance(self.rtl.sc, LEX.Auto): # e.g. static
            raise NotImplementedError(self.rtl.sc)
        self.text.append(".globl %s ; %s"%(self.name, self.rtl.decl))
        self.text.append("%s:"%(self.name,))
        self.extend_stack_frame()
        for op in self.rtl.code:
            self.generate_op(op)

## Generate assembler directives for the global variables

class GlobalGenerator(Generator):
    def generate(self):
        for name, (_, typ, size) in self.rtl.stack.items():
            if name not in self.rtl.inits: # can't happen
                raise GenError("Undeclared global", name)
            init = self.rtl.inits[name]
            if init is None:
                self.bss.append(".globl %s ; %s"%(name,typ))
                self.bss.append("%s: .skip %d"%(name, size))
            else:
                self.data.append(".globl %s ; %s"%(name,typ))
                self.data.append("%s:"%(name,))
                if isinstance(init, int):
                    if size == 1:
                        self.data.append("\t.byte %d"%(init&0xff,))
                    else:
                        raise NotImplementedError(size)
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
    allocations = allocator.alloc(parse_tree, tac)
    print "RTL functions:"
    for name, rtl in allocations.items():
        print rtl.sc, name
        print rtl.stack
        print rtl.code
        print
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
        print ".bss"
        for line in bss:
            print line
    if data:
        print ".data"
        for line in data:
            print line
    if text:
        print ".text"
        for line in text:
            print line

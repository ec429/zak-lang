#!/usr/bin/python

import sys, pprint
import parser, tacifier, allocator
LEX = parser.Lexer
PAR = parser.Parser
TAC = tacifier.TACifier
REG = allocator.Register
RTL = allocator.Allocator

## Generate Z80 assembly code from the stack & RTL

class GenError(Exception): pass

class Generator(object):
    def __init__(self, rtl, name):
        self.rtl = rtl
        self.name = name
        self.code = []
    def extend_stack_frame(self):
        if self.rtl.sp > 127:
            raise GenError("Stack too big (%d bytes, max 127)"%(self.rtl.sp,))
        if self.rtl.sp > self.rtl.caller_stack_size:
            self.code.append("\tLD (IY-1),%d"%(self.rtl.sp,))
            # TODO optional stack-frame zeroing (in case of uninitialised variables)?
        elif self.rtl.sp < self.rtl.caller_stack_size: # what the heck?
            raise GenError("Stack shrunk (not allowed)")
    def generate_op(self, op):
        if isinstance(op, RTL.RTLReturn):
            self.code.append("\tRET")
        elif isinstance(op, RTL.RTLFill):
            assert isinstance(op.reg, REG), op
            if self.rtl.is_on_stack(op.name):
                offset, typ, size = self.rtl.stack[op.name]
                if size != op.reg.size:
                    raise GenError("Fill reg %s (%d) with %s (%d)"%(op.reg, op.reg.size, op.name, size))
                if size == 1:
                    self.code.append("\tLD %s,(IY+%d)"%(op.reg, offset))
                elif size == 2:
                    self.code.append("\tLD %s,(IY+%d)"%(op.reg.lo, offset))
                    self.code.append("\tLD %s,(IY+%d)"%(op.reg.hi, offset+1))
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
                    self.code.append("\tLD (IY+%d),%s"%(offset, op.reg))
                elif size == 2:
                    self.code.append("\tLD (IY+%d),%s"%(offset, op.reg.lo))
                    self.code.append("\tLD (IY+%d),%s"%(offset+1, op.reg.hi))
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
                self.code.append("\tLD %s,(%s)"%(op.dst, op.src))
            else:
                raise NotImplementedError(size)
        elif isinstance(op, RTL.RTLMove):
            assert isinstance(op.dst, REG), op
            assert isinstance(op.src, REG), op
            assert op.dst.size == op.src.size, op
            if op.dst.size == 1:
                self.code.append("\tLD %s,%s"%(op.dst, op.src))
            else:
                raise NotImplementedError(size)
        elif isinstance(op, RTL.RTLAdd):
            assert isinstance(op.dst, REG), op
            assert isinstance(op.src, REG), op
            if op.dst.name == 'A': # 8-bit add
                if op.src.size != 1: # should never happen
                    raise GenError("Add A with %s (%d)"%(op.src, op.src.size))
                self.code.append("\tADD %s"%(op.src,))
        else:
            raise NotImplementedError(op)
    def generate(self):
        try:
            if not isinstance(self.rtl.sc, LEX.Auto): # e.g. static
                raise NotImplementedError(self.rtl.sc)
            self.code.append(".globl %s"%(self.name,))
            self.code.append("%s:"%(self.name,))
            self.extend_stack_frame()
            for op in self.rtl.code:
                self.generate_op(op)
        finally:
            print "Code:"
            for line in self.code:
                print " ", line

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
            raise NotImplementedError()
        else:
            print "Generating code for", name
            gen = Generator(rtl, name)
            gen.generate()
            generated[name] = gen

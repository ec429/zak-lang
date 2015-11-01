#!/usr/bin/python

import optparse, pprint
import parser, tacifier, allocator, codegen

def parse_args():
    x = optparse.OptionParser()
    x.add_option('-o', '--output', type='string', default="a.out")
    x.add_option('-D', '--debug', action='store_true')
    opts, args = x.parse_args()
    if len(args) > 1:
        x.error("Multiple input files - only one supported")
    return opts, args

if __name__ == "__main__":
    opts, args = parse_args()
    if args:
        with open(args[0], 'r') as f:
            source = f.read()
    else:
        source = sys.stdin.read()
    parse_tree = parser.parse(source)
    if opts.debug:
        print "Parse globals:"
        pprint.pprint(parse_tree.globals)
        print
    tac = tacifier.tacify(parse_tree)
    if opts.debug:
        print "TAC functions:"
        pprint.pprint(tac.functions)
        print
    assert tac.in_func is None, tac.in_func
    assert len(tac.scopes) == 1
    allocations = allocator.alloc(parse_tree, tac)
    if opts.debug:
        print "RTL functions:"
        for name, rtl in allocations.items():
            print rtl.sc, name
            print rtl.stack
            print rtl.code
            print
        print
    gen = codegen.generate(allocations)
    if opts.debug:
        print "Generated line counts:"
        for name, g in gen.items():
            print name
            g.print_stats()
    bss, data, text = codegen.combine(gen)
    dest = open(opts.output, 'w')
    if opts.debug:
        print "==ASSEMBLY OUTPUT BEGINS HERE=="
    if bss:
        if opts.debug:
            print ".bss"
        print >>dest, ".bss"
        for line in bss:
            if opts.debug:
                print line
            print >>dest, line
    if data:
        if opts.debug:
            print ".data"
        print >>dest, ".data"
        for line in data:
            if opts.debug:
                print line
            print >>dest, line
    if text:
        if opts.debug:
            print ".text"
        print >>dest, ".text"
        for line in text:
            if opts.debug:
                print line
            print >>dest, line

#!/usr/bin/python

import optparse, pprint, sys
import parser, tacifier, allocator, codegen

def parse_args():
    x = optparse.OptionParser()
    x.add_option('-o', '--output', type='string', default="a.out")
    x.add_option('-D', '--debug', action='store_true')
    x.add_option('-n', '--dry-run', action='store_true')
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
    outs = []
    if opts.debug:
        print "==ASSEMBLY OUTPUT BEGINS HERE=="
        outs.append(sys.stdout)
    if not opts.dry_run:
        dest = open(opts.output, 'w')
        outs.append(dest)
    def pr(line):
        for out in outs:
            out.write(line)
            out.write('\n')
    if bss:
        pr(".bss")
        for line in bss:
            pr(line)
    if data:
        pr(".data")
        for line in data:
            pr(line)
    if text:
        pr(".text")
        for line in text:
            pr(line)
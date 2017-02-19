#!/usr/bin/python

import optparse, pprint, sys
import parser, ast_build, tacifier, allocator, codegen

def parse_args():
    x = optparse.OptionParser()
    x.add_option('-o', '--output', type='string', default="out.s")
    x.add_option('-D', '--debug', action='store_true')
    x.add_option('-n', '--dry-run', action='store_true')
    x.add_option('-W', action='append', dest='warnings', default=[])
    x.add_option('-G', action='append', dest='gen_opts', default=[])
    opts, args = x.parse_args()
    def boolean_option(t):
        if t.startswith('no-'):
            return (t[3:], False)
        return (t, True)
    opts.warnings = dict(map(boolean_option, opts.warnings))
    opts.gen_opts = dict(map(boolean_option, opts.gen_opts))
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
    if opts.debug: print "-LEX/PARSE-"
    parse_tree = parser.parse(source)
    if opts.debug:
        print "Parse globals:"
        print parse_tree.dump()
        print
    if opts.debug: print "-AST/BUILD-"
    ast = ast_build.AST_builder(parse_tree)
    if opts.debug:
        print "Syntax tree"
        for decl in ast.decls:
            print decl
        print
    if opts.debug: print "-TACIFY-"
    tac = tacifier.tacify(ast)
    if opts.debug:
        print "TAC functions:"
        pprint.pprint(tac.functions)
        print
    assert tac.in_func is None, tac.in_func
    assert len(tac.scopes) == 1
    if opts.debug: print "-ALLOC/RTL-"
    allocations = allocator.alloc(tac, opts.warnings, debug=opts.debug)
    if opts.debug: print "-CODE/GEN-"
    gen = codegen.generate(allocations, opts.gen_opts, opts.warnings)
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
        if opts.output == '-':
            dest = sys.stdout
        else:
            dest = open(opts.output, 'w')
        outs.append(dest)
    def pr(line):
        for out in outs:
            out.write(line)
            out.write('\n')
    pr("; Compiled zak code; do not edit directly")
    if bss:
        pr("")
        pr(".bss")
        for line in bss:
            pr(line)
    if data:
        pr("")
        pr(".data")
        for line in data:
            pr(line)
    if text:
        pr("")
        pr(".text")
        for line in text:
            pr(line)

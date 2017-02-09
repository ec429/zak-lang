#!/usr/bin/python

import sys, pprint
import parser
PAR = parser.Parser

class ASTError(Exception): pass
class UnhandledEntity(ASTError):
    def __init__(self, entity):
        self.entity = entity
    def __str__(self):
        return "%s\ncould not handle entity" % (self.entity.dump(),)

class Type(object):
    name = None
    def __str__(self):
        return self.name

class Void(Type):
    name = 'void'
class Byte(Type):
    name = 'byte'
class Word(Type):
    name = 'word'

def get_type(typ):
    if typ.get('void') is not None:
        return Void()
    if typ.get('byte') is not None:
        return Byte()
    if typ.get('word') is not None:
        return Word()

class StorageClass(object):
    def __init__(self, sc):
        self.sc = sc
    def __str__(self):
        return self.sc

class Identifier(object):
    def __init__(self, ident, typ):
        self.ident = ident
        self.typ = typ
    def __str__(self):
        return str(self.typ)

def DirectDecl(direct_decl, typ):
    # <direct-decl>   ::= <identifier> | '(' <decl-spec> ')' | <array-decl> | <func-decl>
    if direct_decl.get('identifier') is not None:
        return Identifier(direct_decl['identifier'], typ)
    raise UnhandledEntity(direct_decl)

class Pointer(object):
    # <pointer>       ::= '*' <qualifier-list>? <pointer>?
    def __init__(self, pointer, target):
        if pointer.get('qualifier_list') is not None:
            raise UnhandledEntity(pointer['qualifier_list'])
        if pointer.get('pointer') is not None:
            raise UnhandledEntity(pointer.get('pointer'))
        self.target = target
        self.ident = target.ident
    def __str__(self):
        return 'Pointer(%s)'%(self.target,)

class DeclSpec(object):
    def __init__(self, decl_spec, typ):
        # <decl-spec>    ::= <pointer>? <direct-decl>
        direct_decl = DirectDecl(decl_spec['direct_decl'], typ)
        pointer = decl_spec.get('pointer')
        if pointer is not None:
            self.object = Pointer(pointer, direct_decl)
        else:
            self.object = direct_decl
        self.ident = self.object.ident
    def __str__(self):
        return '%s as %s'%(self.ident, self.object)

class Declaration(object):
    # <object-decl>   ::= <decl-spec> <initialiser>
    def __init__(self, declaration, sc, typ):
        self.sc = sc
        self.decl_spec = DeclSpec(declaration['decl_spec'], typ)
        if declaration.get('initialiser') is not None:
            raise UnhandledEntity(declaration['initialiser'])
    def __str__(self):
        if self.sc is None:
            return str(self.decl_spec)
        return '%s %s'%(self.sc, self.decl_spec)

class Declare(object):
    # <declare>       ::= <storage-class>? <qualifier-list>? <type> <declaration>
    def __init__(self, declare):
        self.sc = declare.get('storage_class')
        if self.sc is not None:
            if self.sc.get('static') is not None:
                self.sc = StorageClass('static')
            elif self.sc.get('extern') is not None:
                self.sc = StorageClass('extern')
            elif self.sc.get('auto') is not None:
                self.sc = StorageClass('auto')
            else:
                raise UnhandledEntity(self.sc)
        if declare.get('qualifier_list') is not None:
            raise UnhandledEntity(declare['qualifier_list'])
        self.typ = get_type(declare['type'])
        if self.typ is None:
            raise UnhandledEntity(declare['type'])
        # <declaration>   ::= <object-decls> ';' | <function-defn>
        # <object-decls>  ::= <object-decl> (',' <object-decls>)?
        self.declarations = [Declaration(d, self.sc, self.typ) for d in declare['declaration']]
    def __str__(self):
        return '\n'.join(['declare %s'%(d,) for d in  self.declarations])

class AST_builder(object):
    def __init__(self, parse_tree):
        self.decls = []
        try:
            for entity in parse_tree:
                if entity.get('declare'):
                    self.decls.append(Declare(entity['declare']))
                else:
                    raise UnhandledEntity(entity)
        finally:
            for decl in self.decls:
                print decl

## Test code

if __name__ == "__main__":
    if len(sys.argv) > 1:
        with open(sys.argv[1], 'r') as f:
            source = f.read()
    else:
        source = sys.stdin.read()
    parse_tree = parser.parse(source)
    print "Parse tree:"
    pprint.pprint(parse_tree)
    print
    ast = AST_builder(parse_tree)

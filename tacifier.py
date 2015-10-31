#!/usr/bin/python

import sys, pprint
import parser

class TACError(Exception): pass

class TACifier(object):
	class TACStatement(object): pass
	class TACDeclare(TACStatement):
		def __init__(self, name, size):
			self.name = name
			self.size = size
		def __repr__(self):
			return 'TACDeclare(%r, %r)'%(self.name, self.size)
	class TACAssign(TACStatement):
		def __init__(self, dst, src):
			self.dst = dst
			self.src = src
		def __repr__(self):
			return 'TACAssign(%r, %r)'%(self.dst, self.src)
	class TACAdd(TACStatement):
		def __init__(self, dst, src):
			self.dst = dst
			self.src = src
		def __repr__(self):
			return 'TACAdd(%r, %r)'%(self.dst, self.src)
	class TACReturn(TACStatement):
		def __init__(self, src):
			self.src = src
		def __repr__(self):
			return 'TACReturn(%r)'%(self.src,)
	class FuncParam(object):
		pass
	class Value(object):
		def __init__(self, typ):
			self.typ = typ
		def __repr__(self):
			return 'Value(%r)'%(self.typ,)
	class Identifier(Value):
		def __init__(self, typ, name):
			super(TACifier.Identifier, self).__init__(typ)
			self.name = name
		def __repr__(self):
			return 'Identifier(%r, %r)'%(self.typ, self.name)
	def __init__(self):
		self.scopes = [{}]
		self.functions = {None:[]}
		self.in_func = None
	def arg_list(self, arglist):
		scope = {}
		for name,typ in arglist.args:
			if name in scope:
				raise TACError("Name", name, "redeclared within parameter list")
			scope[name] = (parser.Lexer.Auto("auto"), typ, self.FuncParam())
		return scope
	def get_lvalue(self, lval):
		if isinstance(lval, parser.Parser.IdentifierExpression):
			for scope in reversed(self.scopes):
				if lval.name in scope:
					sc, typ, init = scope[lval.name]
					return (self.Identifier(typ, lval.name), [])
		else:
			pprint.pprint(lval)
			raise NotImplementedError()
	def get_rvalue(self, rval):
		if isinstance(rval, parser.Parser.IdentifierExpression):
			for scope in reversed(self.scopes):
				if rval.name in scope:
					sc, typ, init = scope[rval.name]
					return (self.Identifier(typ, rval.name), [])
		else:
			pprint.pprint(rval)
			raise NotImplementedError()
	def emit_assignish(self, op, lvalue, rvalue):
		if isinstance(lvalue, self.Identifier):
			if isinstance(rvalue, self.Identifier):
				if lvalue.typ != rvalue.typ:
					raise TACError("Type mismatch assigning", rvalue, "to", lvalue)
				if isinstance(op, parser.Lexer.Add):
					return [self.TACAdd(lvalue.name, rvalue.name)]
				raise NotImplementedError(op)
			raise TACError("Uninterpreted rvalue", rvalue)
		raise TACError("Uninterpreted lvalue", lvalue)
	def emit_return(self, rvalue):
		if self.in_func is None:
			raise TACError("return outside function")
		decl = self.in_func[1]
		typ = decl.bound
		if isinstance(rvalue, self.Identifier):
			if typ != rvalue.typ:
				raise TACError("Type mismatch returning", rvalue, "from", decl)
			return [self.TACReturn(rvalue.name)]
		raise TACError("Uninterpreted rvalue", rvalue)
		raise NotImplementedError()
	def walk_expr(self, expr):
		if isinstance(expr, parser.Parser.IdentifierExpression):
			return self.get_rvalue(expr)
		if isinstance(expr, parser.Parser.AssignIsh):
			op = expr.op
			lval = expr.left
			rval = expr.right
			lvalue, ls = self.get_lvalue(lval)
			rvalue, rs = self.get_rvalue(rval)
			return (lvalue, ls + rs + self.emit_assignish(op, lvalue, rvalue)) # lvalue becomes an rvalue
		pprint.pprint(expr)
		raise NotImplementedError()
	def walk_stmt(self, stmt):
		if isinstance(stmt, parser.Parser.ExpressionStatement):
			_, stmts = self.walk_expr(stmt.expr)
			return stmts
		elif isinstance(stmt, parser.Parser.ReturnStatement):
			rvalue, stmts = self.walk_expr(stmt.expr)
			return stmts + self.emit_return(rvalue)
		else:
			pprint.pprint(stmt)
			raise NotImplementedError()
	def walk(self, block):
		func = []
		for declaration in block.local:
			pprint.pprint(declaration)
			raise NotImplementedError()
		for stmt in block.body:
			func.extend(self.walk_stmt(stmt))
		return func
	def add(self, name, sc, decl, init):
		if isinstance(decl, parser.Parser.FunctionDecl) and isinstance(init, parser.Parser.BlockStatement):
			if isinstance(sc, parser.Lexer.Extern):
				raise TACError("extern function with definition")
			if self.in_func is not None: # should be impossible, parser won't allow it
				raise TACError("Nested function definition")
			self.in_func = (name, decl)
			self.scopes.append(self.arg_list(decl.arglist))
			func = self.walk(init)
			self.scopes.pop(-1)
			self.in_func = None
			self.functions[name] = func
			self.scopes[-1][name] = (sc, decl, func)
		else:
			raise NotImplementedError()

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
	tac = TACifier()
	for (name, sc, decl, init) in parse_tree.globals:
		tac.add(name, sc, decl, init)
	print "TAC scopes:"
	pprint.pprint(tac.scopes)
	print "TAC functions:"
	pprint.pprint(tac.functions)
	assert tac.in_func is None, tac.in_func

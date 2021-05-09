import re

lex = lambda s: re.findall(r'-?[0-9]+\.?[0-9]*|[a-zA-Z_+-/*<>=!]+|\(|\)|\'|"[^"]*"', s)

class Symbol(str):
    def __repr__(self):
        return f'<{self}>'

class Quoted:
    def __init__(self, x):
        self.x = x

    def __repr__(self):
        return "'" + repr(self.x)

def atom(tok):
    try:
        return int(tok)
    except ValueError:
        try:
            return float(tok)
        except ValueError:
            if tok[0] == '"' and tok[-1] == '"':
                return tok[1:-1]
            return Symbol(tok)

def _parse(toks):
    if toks[0] == '(':
        toks = toks[1:]
        expr = []
        while toks[0] != ')':
            x, toks = _parse(toks)
            expr.append(x)
        return expr, toks[1:]
    elif toks[0] == "'":
        expr, toks = _parse(toks[1:])
        return Quoted(expr), toks
    else:
        return atom(toks[0]), toks[1:]

def parse(s):
    expr, toks = _parse(lex(s))
    if toks:
        raise ValueError('failed to fully parse expression')
    return expr

ops = {'+', '-', '*', '/', '<', '<=', '==', '!=', '>', '>='}

binops = {'+': 'BINARY_ADD', '-': 'BINARY_SUBTRACT', '*': 'BINARY_MULTIPLY', '/': 'BINARY_TRUE_DIVIDE'}
unops = {'+': 'UNARY_POSITIVE', '-': 'UNARY_NEGATIVE'}

import types, dis

class Compiler:
    def __init__(self):
        self.co_consts = []
        self.co_names = []
        self.bs = []
        self.name = ''
        self.args = []
        self.assignment = False

    def to_code_object(self):
        return types.CodeType(
            len(self.args), # argcount
            0, # posonlyargcount
            0, # kwonlyargcount
            len(self.args), # nlocals
            32, # stacksize
            0, # flags
            self.to_codestring(), # codestring
            tuple(self.co_consts), # constants
            tuple(self.co_names), # names
            tuple(self.args), # varnames
            '', # filename
            self.name, # name
            0, # firstlineno
            b'', # lnotab
            (), # freevars
            () # cellvars
        )

    def to_func_object(self):
        return types.FunctionType(
            self.to_code_object(), # code
            globals(), # globals
            self.name # name
        )

    def to_codestring(self):
        self.bs.append(dis.opmap['RETURN_VALUE'])
        self.bs.append(0)
        return bytes(self.bs)

    def emit(self, *args):
        if len(args) == 1:
            self.bs.append(dis.opmap[args[0]])
            self.bs.append(0)
        elif len(args) == 2:
            self.bs.append(dis.opmap[args[0]])
            self.bs.append(args[1])

    def add_name(self, name):
        if name in self.co_names:
            return self.co_names.index(name)
        self.co_names.append(name)
        return len(self.co_names)-1

    def compile(self, expr):
        if type(expr) == list:
            if expr[0] == 'def':
                if type(expr[1]) == list:
                    self.name, *self.args = expr[1]
                else:
                    self.name = expr[1]
                    self.assignment = True
                self.compile(expr[2])
            elif expr[0] == 'if':
                self.compile_if(expr[1], expr[2], expr[3])
            elif expr[0] in ops:
                self.compile_op(expr[0], expr[1:])
            else:
                self.compile_funcall(expr[0], expr[1:])
        elif type(expr) == Quoted:
            self.compile_atom(expr.x)
        else:
            self.compile_atom(expr)

    def compile_if(self, cond, then, _else):
        self.compile(cond)
        self.emit('POP_JUMP_IF_FALSE', 0)
        i = len(self.bs)-1
        self.compile(then)
        self.emit('JUMP_FORWARD', 0)
        j = len(self.bs)-1
        self.compile(_else)
        self.bs[i] = j+1
        self.bs[j] = len(self.bs)-j-1

    # TODO: handle multiple arguments
    def compile_op(self, op, args):
        if len(args) == 1:
            self.compile(args[0])
            self.emit(unops[op])
        elif op in binops:
            self.compile(args[0])
            self.compile(args[1])
            self.emit(binops[op])
            for arg in args[2:]:
                self.compile(arg)
                self.emit(binops[op])
        elif op in {'<', '<=', '==', '!=', '>', '>='}:
            self.compile(args[0])
            self.compile(args[1])
            self.emit('COMPARE_OP', dis.cmp_op.index(op))
            for arg in args[2:]:
                self.compile(arg)
                self.emit('COMPARE_OP', dis.cmp_op.index(op))

    def compile_funcall(self, func, args):
        self.emit('LOAD_GLOBAL', self.add_name(func))
        for arg in args:
            self.compile(arg)
        self.emit('CALL_FUNCTION', len(args))

    def compile_atom(self, atom):
        if type(atom) == Symbol:
            if atom in self.args:
                self.emit('LOAD_FAST', self.args.index(atom))
            else:
                self.emit('LOAD_GLOBAL', self.add_name(atom))
        else:
            self.co_consts.append(atom)
            self.emit('LOAD_CONST', len(self.co_consts)-1)

def lisp_compile(s):
    c = Compiler()
    c.compile(parse(s))
    return c.to_code_object()

def lisp_eval(s):
    c = Compiler()
    c.compile(parse(s))
    if c.name:
        if c.assignment:
            globals()[str(c.name)] = eval(c.to_code_object())
            return globals()[str(c.name)]
        globals()[str(c.name)] = c.to_func_object()
    else:
        return eval(c.to_code_object())

def lisp_repl():
    while 1:
        try:
            print(' ', lisp_eval(input('> ')))       # ???
        except KeyboardInterrupt:
            break
        except EOFError:
            break
        except Exception as e:
            print(e)

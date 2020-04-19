# Author: Robbert van Renesse, 2020

import os
import random
import traceback

pluspypath = ".:./modules/lib:./modules/book:./modules/other"

def exit(status):
    sys.stdout.flush()
    os._exit(status)

# When compiling and running into an identifier, it should be clear
# exactly what that identifier refers to.  It could be the name of:
#
#   - a variable
#   - a constant
#   - an operator
#   - an argument of that operator
#   - a bounded variable (\E, ...)
#   - a module
#
# In order to do this mapping, we keep a stack of dictionaries
# that map names to expressions for these things.
name_stack = [{}]

def name_lookup(name):
    for d in reversed(name_stack):
        ex = d.get(name)
        if ex != None:
            return ex
    return False

# Like name_lookup but prints an error
def name_find(name):
    e = name_lookup(name)
    if not e:
        print("Identifier", name, "not found")
    return e

# Find a file using a directory path
def file_find(name, path):
    sep = ";" if path.find(";") >= 0 else ":"
    for dir in path.split(sep):
        full = os.path.join(dir, name)
        if os.path.exists(full):
            return os.path.abspath(full)
    return None

# For debugging, we give each bounded variable a unique identifier
bv_counter = 0

# kludge: as object definitions are properly nested, I maintain a stack
# of modules
modstk = []

# kludge: for transforming expression for initialization
initializing = False

# This is a dictionary of modules that have already been loaded
# from files.
modules = {}

# This is a dictionary of wrappers around Python functions
# Maps module names to dictionaries of (operator name, Wrapper) pairs
wrappers = {}

# Verbose output
silent = False
verbose = False

class FrozenDict:
    def __init__(self, d):
        self.d = d

    def __str__(self):
        return "FrozenDict(" + str(self.d) + ")"

    def __hash__(self):
        hash = 0
        for x in self.d.items():
            hash ^= x.__hash__()
        return hash

    # Two dictionaries are the same if they have the same (key, value) pairs
    def __eq__(self, other):
        if not isinstance(other, FrozenDict):
            return False
        if len(self.d.keys()) != len(other.d.keys()):
            return False
        for (k, v) in self.d.items():
            if v != other.d.get(k):
                return False
        return True

    def __len__(self):
        return len(self.d.keys())

    def format(self):
        result = ""
        keys = sorted(self.d.keys(), key=lambda x: key(x))
        for k in keys:
            if result != "":
                result += ", "
            if is_tla_id(k):
                result += k + " |-> " + format(self.d[k])
            else:
                result += format(k) + " |-> " + format(self.d[k])
        return "[ " + result + " ]"

# A Hashable "nonce" (to implement CHOOSE x: x \notin S)
class Nonce:
    def __init__(self, id):
        self.id = id            # TODO: ideally a cryptographic hash

    def __str__(self):
        return "Nonce(" + str(self.id) + ")"

    def __hash__(self):
        return self.id

    def __eq__(self, other):
        return isinstance(other, Nonce) and other.id == self.id

#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 
####    Module specification
#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 

class Module:
    def __init__(self):
        self.name = None
        self.constants = dict()     # name -> ConstantExpression
        self.variables = dict()     # name -> VariableExpression
        self.operators = dict()     # name -> OperatorExpression
        self.wrappers = dict()      # name -> BuiltinExpression
        self.globals = set()        # set of non-LOCAL names

    def __str__(self):
        return "Module(" + self.name + ", " + str(self.constants) \
            + ", " + str(self.variables) + ", " \
            + str(self.operators.keys()) + ")"

    # handle a CONSTANT declaration
    def compileConstantDeclaration(self, ast):
        (t0, a0) = ast
        assert t0 == "CommaList"
        for (t1, a1) in a0:
            assert t1 == "GOpDecl"
            (t2, a2) = a1
            if t2 == "Identifier":
                id = lexeme(a2)
                nargs = 0
            elif t2 == "paramOp":
                (t3, a3) = a2[0]
                assert t3 == "Identifier"
                (t4, a4) = a2[1]
                assert t4 == "CommaList"
                id = lexeme(a3)
                nargs = len(a4)
            elif t2 == "prefixOp" or t2 == "postfixOp":
                id = a2
                nargs = 1
            elif t2 == "infixOp":
                id = a2
                nargs = 2
            else:
                assert False
            ce = ConstantExpression(id, nargs)
            self.constants[id] = ce
            name_stack[-1][id] = ce

    # handle a VARIABLE declaration
    def compileVariableDeclaration(self, ast):
        (t, a) = ast
        assert t == "CommaList"
        for (t2, a2) in a:
            assert t2 == "Identifier"
            id = lexeme(a2)
            ve = VariableExpression(id)
            self.variables[id] = ve
            name_stack[-1][id] = ve

    # handle an "Operator == INSTANCE name" definition
    def compileModuleDefinition(self, md, isGlobal):
        (t0, a0) = md[0]
        assert t0 == "GNonFixLHS"
        assert len(a0) == 2
        inst = md[1]

        (t2, a2) = a0[0]
        assert t2 == "Identifier"
        id = lexeme(a2)
        (t3, a3) = a0[1]
        assert t3 == "Optional"
        if a3 == None:
            args = []
        else:
            (t4, a4) = a3
            assert t4 == "CommaList"
            args = a4

        cargs = []
        for (t, a) in args:
            assert t == "GOpDecl"
            (t2, a2) = a
            if t2 == "Identifier":
                cargs = cargs + [(lexeme(a2), 0)]
            elif t2 == "paramOp":
                (t3, a3) = a2[0]
                assert t3 == "Identifier"
                (t4, a4) = a2[1]
                assert t4 == "CommaList"
                cargs = cargs + [(lexeme(a3), len(a4))]
            elif t2 == "prefixOp" or t2 == "postfixOp":
                cargs = cargs + [(a2, 1)]
            elif t2 == "infixOp":
                cargs = cargs + [(a2, 2)]
            else:
                assert False

        # print("MD 1", id)

        mi = ModInst()
        args = [ArgumentExpression(a, c) for (a, c) in cargs]
        name_stack.append({ a.id:a for a in args })
        # print("MD 2", id, inst)
        mi.compile(inst)
        # print("MD 3", id, args, mi)
        name_stack.pop()

        # We put the ModInst inside the expr field of an OperatorExpression
        od = OperatorExpression(id=id, args=args, expr=mi)
        self.operators[id] = od
        if isGlobal:
            self.globals.add(id)
        name_stack[-1][id] = od
        if verbose:
            print("++> ", od, mi)

    # handle the next TLA "Unit" in the source
    def compileUnit(self, ast):
        (t, a) = ast
        if t == "GVariableDeclaration":
            self.compileVariableDeclaration(a)
        elif t == "GConstantDeclaration":
            self.compileConstantDeclaration(a)
        elif t == "decl-op":
            (tloc, aloc) = a[0]
            assert tloc == "Optional"
            (t1, a1) = a[1]
            assert t1 == "GOperatorDefinition"
            (id, args, expr) = compileOperatorDefinition(a1)
            if id in self.wrappers.keys():
                od = OperatorExpression(id, args,
                            BuiltinExpression(id, args, self.wrappers[id]))
            else:
                od = OperatorExpression(id, args, expr)
            self.operators[id] = od
            if aloc == None:
                self.globals.add(id)
            name_stack[-1][id] = od.expr if args == [] else od
            if verbose:
                print("+-> ", id, args, expr.primed, expr)
        elif t == "decl-inst":
            (tloc, aloc) = a[0]
            assert tloc == "Optional"
            mi = ModInst()
            mi.compile(a[1])
            for k in mi.globals:
                self.operators[k] = mi.operators[k]
                if aloc == None:
                    self.globals.add(k)
        elif t == "decl-fun":
            (tloc, aloc) = a[0]
            assert tloc == "Optional"
            (t1, a1) = a[1]
            assert t1 == "GFunctionDefinition"
            (id, args, expr) = compileFunctionDefinition(a1)
            od = OperatorExpression(id, args, expr)
            self.operators[id] = od
            if aloc == None:
                self.globals.add(id)
            assert args == []
            # name_stack[-1][id] = od
            name_stack[-1][id] = expr
            if verbose:
                print("++> ", id, args, expr.primed, expr)
        elif t == "decl-mod":
            (tloc, aloc) = a[0]
            assert tloc == "Optional"
            (t1, a1) = a[1]
            assert t1 == "GModuleDefinition"
            self.compileModuleDefinition(a1, tloc != None)
        elif t in { "GTheorem", "GAssumption", "GDivider" }:
            pass
        elif t == "GModule":
            mod = Module()
            mod.compile(ast)
            name_stack[-1][mod.name] = mod
        else:
            print("compileUnit", ast)
            assert False

    # Get operators from EXTENDS clause
    def extends(self, ast):
        for (n, m) in ast:
            assert n == "Name"
            mod = load_module(lexeme(m))
            assert mod.constants == dict()
            assert mod.variables == dict()
            for k in mod.globals:
                self.operators[k] = mod.operators[k]
                self.globals.add(k)
                if mod.wrappers.get(k) != None:
                    self.wrappers[k] = mod.wrappers[k]
                name_stack[-1][k] = mod.operators[k]

    # Given AST, handle all the TLA+ units in the AST
    def compile(self, ast):
        (t, a) = ast
        if t == False:
            return False
        assert t == "GModule"
        assert len(a) == 3
        (t0, a0) = a[0]
        assert t0 == "Name"
        self.name = lexeme(a0)

        # Set wrappers
        global wrappers
        self.wrappers = wrappers.get(self.name)
        if self.wrappers == None:
            self.wrappers = {}

        # Add a new dictionary to the name stack
        name_stack.append({})

        (t1, a1) = a[1]
        assert t1 == "Optional"
        if a1 != None:
            (tx, ax) = a1
            assert tx == "CommaList"
            self.extends(ax)

        (t2, a2) = a[2]
        assert t2 == "AtLeast0"
        for ast2 in a2:
            self.compileUnit(ast2)

        if verbose:
            print("Variables", self.name, self.variables)

        name_stack.pop()
        return True

    # Load and compile the given TLA+ source, which is a string
    def load_from_string(self, source, srcid):
        # First run source through lexical analysis
        r = lexer(source, srcid)
        if verbose:
            print()
            print("---------------")
            print("Output from Lexer")
            print("---------------")
            print(r)

        # Parse the output from the lexer into an AST
        gmod = GModule()

        # Error handling
        global shortest, error
        shortest = r

        (t, a, r) = gmod.parse(r)
        # t is the type of the AST root node (False if error)
        # a is the content (or error message list if error)
        # r is the suffix of the lexer output that could not be parsed

        if False:
            print()
            print("---------------")
            print("AST")
            print("---------------")
            printAST((t, a), "")

        if t == False:
            print("Parsing failed", a)
            print(error)
            print("At position", shortest[0])
            return False

        if r != []:
            print("Remainder", r[0])

        # Handle all TLA+ units in the AST
        if verbose:
            print()
            print("---------------")
            print("Compile", source.split("\n")[0].replace("-", ""))
            print("---------------")

        modstk.append(self)
        result = self.compile((t, a))
        modstk.pop()

        return result

    def load(self, f, srcid):
        all = ""
        for line in f:
           all += line
        return self.load_from_string(all, srcid)

    def load_from_file(self, file):
        full = file_find(file, pluspypath)
        if full == None:
            print("can't find", file, ": fatal error", file=sys.stderr)
            exit(1)
        with open(full) as f:
            return self.load(f, file)

def load_module(name):
    mod = name_lookup(name)
    if mod == False:
        if modules.get(name) == None:
            mod = Module()
            name_stack.append({})
            mod.load_from_file(name + ".tla")
            name_stack.pop()
            modules[name] = mod
        else:
            mod = modules[name]
    return mod

#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 
####    Module instance
#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 

# Describes an "INSTANCE module-name WITH k <- e ..." expression.
# Here each k is either a constant or variable name of the module, and e
# some expression that should be substituted for it
class ModInst:
    def __init__(self, module=None, substitutions=None, operators=None, wrappers=None, globals=None):
        self.module = module
        self.substitutions = substitutions
        self.operators = operators
        self.wrappers = wrappers
        self.globals = globals
        self.primed = False

    def __str__(self):
        subs = ""
        for (k, v) in self.substitutions.items():
            if subs != "":
                subs += ", "
            subs += str(k) + ": " + str(v)
        return "Instance(" + self.module.name + ", [" + subs + "])"

    def __repr__(self):
        return self.__str__()

    def substitute(self, subs):
        substitutions = {
            k:v.substitute(subs) for (k, v) in self.substitutions.items()
        }
        return ModInst(module=self.module, substitutions=substitutions, operators={}, globals=set())

    def set(self, module, substitutions):
        self.module = module
        self.substitutions = substitutions

    def compile(self, ast):
        (t, a) = ast
        assert t == "GInstance"
        (t1, a1) = a[0]
        assert t1 == "Name"
        self.module = load_module(lexeme(a1))

        (t2, a2) = a[1]
        assert t2 == "Optional"
        d = {}
        if a2 != None:
            (t3, a3) = a2
            assert t3 == "CommaList"
            for (t4, a4) in a3:
                assert t4 == "GSubstitution"
                (t5, a5) = a4[0]
                assert t5 == "Identifier"
                (t6, a6) = a4[1]
                assert t6 == "GArgument"
                d[lexeme(a5)] = compileExpression(a6)

        # We now need to replace all the constants and variables in the
        # operators of the module.  Some may have been specified using
        # WITH (captured in 'd'), others are implicit.

        self.substitutions = {}
        for (k, v) in self.module.constants.items():
            if k in d.keys():
                self.substitutions[v] = d[k]
            else:
                self.substitutions[v] = name_find(k)
        for (k, v) in self.module.variables.items():
            if k in d.keys():
                self.substitutions[v] = d[k]
            else:
                self.substitutions[v] = name_find(k)
        self.operators = {}
        self.globals = set()
        self.wrappers = {}
        for k in self.module.globals:
            assert k not in self.globals
            assert self.operators.get(k) == None
            d = self.module.operators[k]
            self.operators[k] = d.substitute(self.substitutions)
            # print("AAA", k, d, self.operators[k])
            self.globals.add(k)
            if self.module.wrappers.get(k) != None:
                self.wrappers[k] = self.module.wrappers[k]

#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 
####    Compiler: convenient routines
#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 

def islower(c):
    return c in "abcdefghijklmnopqrstuvwxyz"

def isupper(c):
    return c in "ABCDEFGHIJKLMNOPQRSTUVWXYZ"

def isletter(c):
    return islower(c) or isupper(c)

def isnumeral(c):
    return c in "0123456789"

def isalnum(c):
    return isletter(c) or isnumeral(c)

def isnamechar(c):
    return isalnum(c) or c == "_"

def isprint(c):
    return isinstance(c, str) and len(c) == 1 and (
        isalnum(c) or c in " ~`!@#$%^&*()-_=+[{]}\\|;:'\",<.>/?")

#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 
####    Compiler: various tables copied from book
#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 

ReservedWords = [
    "ASSUME", "ELSE", "LOCAL", "UNION", "ASSUMPTION", "ENABLED", "MODULE",
    "VARIABLE", "AXIOM", "EXCEPT", "OTHER", "VARIABLES", "CASE", "EXTENDS",
    "CHOOSE", "IF", "SUBSET", "WITH", "CONSTANT", "IN", "THEN", "CONSTANTS",
    "INSTANCE", "THEOREM", "DOMAIN", "LET", "UNCHANGED", "SF_", "WF_"
]

PrefixOps = {
    "-":            (12, 12),
    "-.":           (12, 12),
    "~":             (4,  4),
    "\\lnot":        (4,  4),
    "\\neg":         (4,  4),
    "[]":            (4, 15),
    "<>":            (4, 15),
    "DOMAIN":        (9,  9),
    "ENABLED":       (4, 15),
    "SUBSET":        (8,  8),
    "UNCHANGED":     (4, 15),
    "UNION":         (8,  8)
}

InfixOps = {
    "!!":            (9, 13),
    "#":             (5,  5),
    "##":            (9, 13),
    "$":             (9, 13),
    "$$":            (9, 13),
    "%":            (10, 11),
    "%%":           (10, 11),
    "&":            (13, 13),
    "&&":           (13, 13),
    "(+)":          (10, 10),
    "(-)":          (11, 11),
    "(.)":          (13, 13),
    "(/)":          (13, 13),
    "(\\X)":        (13, 13),
    "*":            (13, 13),
    "**":           (13, 13),
    "+":            (10, 10),
    "++":           (10, 10),
    "-":            (11, 11),
    "-+->":          (2,  2),
    "--":           (11, 11),
    "-|":            (5,  5),
    "..":            (9,  9),
    "...":           (9,  9),
    "/":            (13, 13),
    "//":           (13, 13),
    "/=":            (5,  5),
    "/\\":           (3,  3),
    "::=":           (5,  5),
    ":=":            (5,  5),
    ":>":            (7,  7),
    "<":             (5,  5),
    "<:":            (7,  7),
    "<=>":           (2,  2),
    "=":             (5,  5),
    "<=":            (5,  5),
    "=<":            (5,  5),
    "=>":            (1,  1),
    "=|":            (5,  5),
    ">":             (5,  5),
    ">=":            (5,  5),
    "??":            (9, 13),
    "@@":            (6,  6),
    "\\":            (8,  8),
    "\\/":           (3,  3),
    "^":            (14, 14),
    "^^":           (14, 14),
    "|":            (10, 11),
    "|-":            (5,  5),
    "|=":            (5,  5),
    "||":           (10, 11),
    "~>":            (2,  2),
    ".":            (17, 17),
    "\\approx":      (5,  5),
    "\\geq":         (5,  5),
    "\\oslash":     (13, 13),
    "\\sqsupseteq":  (5,  5),
    "\\asymp":       (5,  5),
    "\\gg":          (5,  5),
    "\\otimes":     (13, 13),
    "\\star":       (13, 13),
    "\\bigcirc":    (13, 13),
    "\\in":          (5,  5),
    "\\notin":       (5,  5),
    "\\prec":        (5,  5),
    "\\subset":      (5,  5),
    "\\bullet":     (13, 13),
    "\\intersect":   (8,  8),
    "\\preceq":      (5,  5),
    "\\subseteq":    (5,  5),
    "\\cap":         (8,  8),
    "\\land":        (3,  3),
    "\\propto":      (5,  5),
    "\\succ":        (5,  5),
    "\\cdot":        (5, 14),
    "\\leq":         (5,  5),
    "\\sim":         (5,  5),
    "\\succeq":      (5,  5),
    "\\circ":       (13, 13),
    "\\ll":          (5,  5),
    "\\simeq":       (5,  5),
    "\\supset":      (5,  5),
    "\\cong":        (5,  5),
    "\\lor":         (3,  3),
    "\\sqcap":       (9, 13),
    "\\supseteq":    (5,  5),
    "\\cup":         (8,  8),
    "\\o":          (13, 13),
    "\\sqcup":       (9, 13),
    "\\union":       (8,  8),
    "\\div":        (13, 13),
    "\\odot":       (13, 13),
    "\\sqsubset":    (5,  5),
    "\\uplus":       (9, 13),
    "\\doteq":       (5,  5),
    "\\ominus":     (11, 11),
    "\\sqsubseteq":  (5,  5),
    "\\wr":          (9, 14),
    "\\equiv":       (2,  2),
    "\\oplus":      (10, 10),
    "\\sqsupset":    (5,  5),

    # The following are Cartesian product ops, not infix operators
    "\\X":          (10, 13),
    "\\times":      (10, 13)
}

PostfixOps = {
    "[":   (16, 16),
    "^+":  (15, 15),
    "^*":  (15, 15),
    "^#":  (15, 15),
    "'":   (15, 15)
}

#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 
####    Compiler: AST pretty printer
#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 

# For printAST: AST nodes that have lists of nodes as arguments
listNodes = [
    "Concat", "Index", "GModule", "AtLeast0", "AtLeast1", "CommaList",
    "GOperatorDefinition", "GQuantifierBound",
    "op", "lambda", "except", "if", "forall", "exists", "square"
]

# printAST: AST nodes that have another AST node as argument
tagNodes = [
    "GUnit", "GTheorem", "GBasicExpression", "GExpression18", "GArgument",
    "GVariableDeclaration", "GConstantDeclaration", "Tuple",
    "parentheses", "set", "wf", "sf"
]

# Pretty printer for AST.  Every node in the AST is of the form (t, a),
# where 't' is the type and 'a' is what's in the node
def printAST(x, indent):
    (t, a) = x
    if not t:
        print("ERROR: " + str(a))
        return
    print(indent + "(" + t + ",", end="")
    if t in listNodes:
        print()
        print(indent + ".[")
        for y in a:
            printAST(y, indent + "..")
        print(indent + ".]")
        print(indent + ")")
    elif t in tagNodes:
        print()
        printAST(a, indent + "..")
        print(indent + ")")
    elif t.startswith("Infix"):
        (op, lhs, rhs) = a
        print(" " + op + ":")
        printAST(lhs, indent + "..")
        printAST(rhs, indent + "..")
        print(indent + ")")
    elif t.startswith("Prefix"):
        (op, expr) = a
        print(" " + op + ":")
        printAST(expr, indent + "..")
        print(indent + ")")
    elif t.startswith("Postfix"):
        (expr, op) = a
        print(" " + op + ":")
        printAST(expr, indent + "..")
        print(indent + ")")
    elif t == "Optional":
        if a == None:
            print(" None)")
        else:
            print()
            printAST(a, indent + "..")
            print(indent + ")")
    else:
        print(" '" + str(a) + "'", end="")
        print(")")

#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 
####    Compiler: BNF rules
#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 

# Extract the lexeme out of a token
def lexeme(token):
    (lex, line, column, first) = token
    return lex

stack = []      # Global parser state used for parsing disjuncts and conjuncts

# For error messages
shortest = []
error = []

def parseError(a, r):
    global shortest, error
    if len(r) < len(shortest):
        error = a
        shortest = r
    return (False, a, r)

# BNF rule
class Rule:
    # s is a list of tokens.  Returns (t, a, r) where
    #   t: type of the AST node (or False if not recognized)
    #   a: contents of the AST node (or error message if t = False)
    #   r: remainder of 's' that was not parsed
    # Must be redefined in child class
    def parse(self, s):
        return parseError(["Rule.parse undefined"], s)

    # Handy routine for rules that simply call other rules
    # It parses s using the given rule and returns a node (name, (t, a), r)
    # where name is the type of the AST node and (t, a) the result of
    # parsing given the rule.
    #
    # If t is a "Concat" rule (sequence of other rules), then you can
    # select a subset using the select argument
    #
    # Otherwise, if select is not None, the result of the rule is
    # directly returned without adding a new AST node
    def match(self, name, s, rule, select=None):
        (t, a, r) = rule.parse(s)
        if not t:
            return parseError([name] + a, r)
        if isinstance(select, list) and t == "Concat":
            if len(select) == 1:
                return (name, a[select[0]], r)
            return (name, [ a[i] for i in select ], r)
        if select != None:
            return (t, a, r)
        return (name, (t, a), r)

class GModule(Rule):
    def parse(self, s):
        return self.match("GModule", s, Concat([
            tok("----"), tok("MODULE"), Name(), tok("----"),
            Optional(Concat([ tok("EXTENDS"), CommaList(Name()) ]), [1]),
            AtLeast(GUnit(), 0), tok("====")
        ]), [ 2, 4, 5 ])

# This rule recognizes a list of other rules:  rule1 & rule2 & rule3 & ...
class Concat(Rule):
    def __init__(self, what):
        self.what = what

    def parse(self, s):
        rem = s
        result = []
        for x in self.what:
            (t, a, r) = x.parse(rem)
            if not t:
                return parseError(["Concat"] + a, r)
            result = result + [(t, a)]
            rem = r
        return ("Concat", result, rem)

# This rule recognizes a list of at least count rules
class AtLeast(Rule):
    def __init__(self, rule, count):
        self.rule = rule
        self.count = count

    def parse(self, s):
        rem = s
        result = []
        c = self.count
        while True:
            (t, a, r) = self.rule.parse(rem)
            if not t:
                if c > 0:
                    return parseError(["AtLeast" + str(self.count)] + a, r)
                else:
                    return ("AtLeast" + str(self.count), result, rem)
            result = result + [(t, a)]
            rem = r
            c -= 1

# Recognizes an optional rule, i.e., 'rule?'
# 'select' can be used similarly as in Rule.match()
class Optional(Rule):
    def __init__(self, rule, select=None):
        self.rule = rule
        self.select = select

    def parse(self, s):
        (t, a, r) = self.rule.parse(s)
        if not t:
            return ("Optional", None, s)
        elif t == "Concat" and isinstance(self.select, list):
            if len(self.select) == 1:
                return ("Optional", a[self.select[0]], r)
            return ("Optional", [ a[i] for i in self.select ], r)
        else:
            return ("Optional", (t, a), r)

class tok(Rule):
    def __init__(self, what):
        self.what = what

    def parse(self, s):
        if s == []:
            return parseError(["tok: no more tokens"], s)
        if lexeme(s[0]) == self.what:
            return ("tok", s[0], s[1:])
        return parseError([("tok: no match with '" + self.what + "'",
                                stringToken(s[0]))], s)

class Tok(Rule):
    def __init__(self, what, name):
        self.what = what
        self.name = name

    def parse(self, s):
        if s == []:
            return parseError(["Tok: no more tokens"], s)
        if lexeme(s[0]) in self.what:
            return ("Tok", s[0], s[1:])
        return parseError(["Tok: no match with " + self.name], s)

class Name(Rule):
    def __init__(self):
        pass

    def parse(self, s):
        if s == []:
            return parseError(["Name"], s)
        lex = lexeme(s[0])
        if lex.startswith("WF_"):
            return parseError([("Name WF_", s[0])], s)
        if lex.startswith("SF_"):
            return parseError([("Name SF_", s[0])], s)
        hasletter = False
        for c in lex:
            if not isnamechar(c):
                return parseError([("Name with bad character", s[0])], s)
            if isletter(c):
                hasletter = True
        if hasletter:
            return ("Name", s[0], s[1:])
        return parseError([("Name with no letter", s[0])], s)

class Identifier(Rule):
    def __init__(self):
        pass

    def parse(self, s):
        (t, a, r) = Name().parse(s)
        if t != "Name":
            return parseError(["Identifier: not a Name"] + a, s)
        lex = lexeme(a)
        if lex in ReservedWords:
            return parseError([("Identifier: Name Reserved", a)], s)
        return ("Identifier", a, r)

# Sometimes it is convenient to give certain rules names.
# A Tag node simply inserts another AST node with the given name
class Tag(Rule):
    def __init__(self, name, rule, select=None):
        self.name = name
        self.rule = rule
        self.select = select

    def parse(self, s):
        return self.match(self.name, s, self.rule, self.select)

class Number(Rule):
    def __init__(self):
        pass

    def parse(self, s):
        if s == []:
            return parseError(["Number"], s)
        lex = lexeme(s[0])
        for c in lex:
            if not isnumeral(c):
                return parseError([("Number", s[0])], s)
        return ("Number", lex, s[1:])

class String(Rule):
    def __init__(self):
        pass

    def parse(self, s):
        if s == []:
            return parseError(["String"], s)
        lex = lexeme(s[0])
        if lex[0] == '"' and lex[-1] == '"':
            return ("String", lex, s[1:])
        return parseError([("String", s[0])], s)

class SeparatorList(Rule):
    def __init__(self, what, sep, optional):
        self.what = what                # expression to match
        self.sep = sep                  # separator token
        self.optional = optional        # empty list allowed

    def parse(self, s):
        (t, a, r) = self.what.parse(s)
        if not t:
            return ("SeparatorList", [], s) if self.optional \
                        else (False, ["SeparatorList"] + a, r)
        rem = r
        result = [(t, a)]
        while True:
            if lexeme(rem[0]) != self.sep:
                return ("SeparatorList", result, rem)
            (t, a, r) = self.what.parse(rem[1:])
            if not t:
                return ("SeparatorList", result, rem)
            result = result + [(t, a)]
            rem = r

class CommaList(Rule):
    def __init__(self, what):
        self.what = what

    def parse(self, s):
        (t, a, r) = self.what.parse(s)
        if not t:
            return parseError(["CommaList"] + a, r)
        rem = r
        result = [(t, a)]
        while True:
            if lexeme(rem[0]) != ",":
                return ("CommaList", result, rem)
            (t, a, r) = self.what.parse(rem[1:])
            if not t:
                return ("CommaList", result, rem)
            result = result + [(t, a)]
            rem = r

class OneOf(Rule):
    def __init__(self, what):
        self.what = what

    def parse(self, s):
        shortest = s            # look for shortest remainder
        result = None
        for grammar in self.what:
            (t, a, r) = grammar.parse(s)
            if t != False:
                if len(r) < len(shortest):
                    shortest = r
                    result = (t, a, r)
        if result == None:
            return parseError([("OneOf: no match", s)], s)
        return result

class Tuple(Rule):
    def __init__(self):
        pass

    def parse(self, s):
        return self.match("Tuple", s, Concat([ tok("<<"),
            # TODO.  Book does not allow empty tuples
            Optional(CommaList(GExpression(0))), tok(">>") ]), [1])

class GUnit(Rule):
    def local(self, tag, decl):
        return Tag(tag, Concat([ Optional(tok("LOCAL")), decl ]), [0, 1])

    def parse(self, s):
        return self.match("GUnit", s, OneOf([
            GVariableDeclaration(),
            GConstantDeclaration(),
            self.local("decl-op", GOperatorDefinition()),
            self.local("decl-fun", GFunctionDefinition()),
            self.local("decl-inst", GInstance()),
            self.local("decl-mod", GModuleDefinition()),
            GAssumption(),
            GTheorem(),
            GModule(),
            GDivider()
        ]), True)

class GDivider(Rule):
    def parse(self, s):
        return self.match("GDivider", s, tok("----"))

class GVariableDeclaration(Rule):
    def parse(self, s):
        return self.match("GVariableDeclaration", s, Concat([
            OneOf([ tok("VARIABLE"), tok("VARIABLES") ]),
            CommaList(Identifier())
        ]), [1])

class GConstantDeclaration(Rule):
    def parse(self, s):
        return self.match("GConstantDeclaration", s, Concat([
            OneOf([ tok("CONSTANT"), tok("CONSTANTS") ]),
            CommaList(GOpDecl())
        ]), [1])

class GOpDecl(Rule):
    def parse(self, s):
        return self.match("GOpDecl", s, OneOf([
            Identifier(),
            Tag("paramOp", Concat([
                Identifier(), tok("("), CommaList(tok("_")), tok(")")
            ]), [0, 2]),
            Tag("prefixOp", Concat([
                Tok(PrefixOps, "prefix operator"), tok("_")
            ]), [0]),
            Tag("infixOp", Concat([
                tok("_"), Tok(InfixOps, "infix operator"), tok("_")
            ]), [1]),
            Tag("postfixOp", Concat([
                tok("_"), Tok(PostfixOps, "postfix operator")
            ]), [1])
        ]))


class GNonFixLHS(Rule):
    def parse(self, s):
        return self.match("GNonFixLHS", s, Concat([
            Identifier(),
            Optional(Concat([ tok("("), CommaList(GOpDecl()), tok(")") ]), [1])
        ]), [0, 1])

class GFunctionDefinition(Rule):
    def parse(self, s):
        return self.match("GFunctionDefinition", s, Concat([
            Identifier(),
            tok("["), CommaList(GQuantifierBound()), tok("]"),
            tok("=="), GExpression(0) ]), [0, 2, 5])

class GOperatorDefinition(Rule):
    def parse(self, s):
        return self.match("GOperatorDefinition", s, Concat([
            OneOf([
                GNonFixLHS(),
                Tag("prefix", Concat([ Tok(PrefixOps, "prefix operator"), Identifier() ])),
                Tag("infix", Concat([ Identifier(), Tok(InfixOps, "infix operator"), Identifier() ])),
                Tag("postfix", Concat([ Identifier(), Tok(PostfixOps, "postfix operator") ])),
            ]), tok("=="), GExpression(0) ]), [0, 2])

class GTheorem(Rule):
    def parse(self, s):
        return self.match("GTheorem", s,
                Concat([ tok("THEOREM"), GExpression(0) ]), [1])

class GAssumption(Rule):
    def parse(self, s):
        return self.match("GAssumption", s, Concat([
            OneOf([ tok("ASSUME"), tok("ASSUMPTION"), tok("AXIOM") ]),
            Optional(Concat([ Identifier(), tok("==") ])),
            GExpression(0)
        ]), [1])

class IdentifierOrTuple(Rule):
    def parse(self, s):
        return self.match("IdentifierOrTuple", s, OneOf([
            Identifier(),
            Tag("Tuple", Concat([
                tok("<<"), CommaList(Identifier()), tok(">>")
            ]), [1]),
        ]), [0])

class GQuantifierBound(Rule):
    def parse(self, s):
        return self.match("GQuantifierBound", s, Concat([
            OneOf([ CommaList(Identifier()), Tuple() ]),
            tok("\\in"), GExpression(0) ]), [0, 2])

class GInstance(Rule):
    def parse(self, s):
        return self.match("GInstance", s, Concat([
            tok("INSTANCE"), Name(), Optional(Concat([
                tok("WITH"), CommaList(GSubstitution())
            ]), [1])
        ]), [1, 2])

class GSubstitution(Rule):
    def parse(self, s):
        return self.match("GSubstitution", s, Concat([
            # TODO.  Can also replace prefix, infix, or postfix ops
            Identifier(), tok("<-"), GArgument()
        ]), [0, 2])

class GArgument(Rule):
    def parse(self, s):
        return self.match("GArgument", s, OneOf([
            GExpression(0),
            Tag("arg-prefix", GGeneralPrefixOp()),
            Tag("arg-infix", GGeneralInfixOp()),
            Tag("arg-postfix", GGeneralPostfixOp())
        ]))

class GInstancePrefix(Rule):
    def parse(self, s):
        return self.match("GInstancePrefix", s,
            AtLeast(Concat([ Identifier(), Optional(
                Concat([ tok("("),

                # TODO. book has GExpression here, but seems wrong
                CommaList(GArgument()),

                tok(")")
            ]), [1]), tok("!") ]), 0))

class GGeneralIdentifier(Rule):
    def parse(self, s):
        return self.match("GGeneralIdentifier", s,
            Concat([ GInstancePrefix(), Identifier() ]))

class GGeneralPrefixOp(Rule):
    def parse(self, s):
        return self.match("GGeneralPrefixOp", s,
            Concat([ GInstancePrefix(), Tok(PrefixOps, "prefix operator") ]))

class GGeneralInfixOp(Rule):
    def parse(self, s):
        return self.match("GGeneralInfixOp", s,
            Concat([ GInstancePrefix(), Tok(InfixOps, "infix operator") ]))

class GGeneralPostfixOp(Rule):
    def parse(self, s):
        return self.match("GGeneralPostfixOp", s,
            Concat([ GInstancePrefix(), Tok(PostfixOps, "postfix operator") ]))

class GModuleDefinition(Rule):
    def parse(self, s):
        return self.match("GModuleDefinition", s,
            Concat([ GNonFixLHS(), tok("=="), GInstance() ]), [0, 2])

# a disjunct or conjunct token is identifier by all but the line in the token
def junct(token):
    (lex, line, column, first) = token
    return (lex, column, first)

# we use the average of the precedence range of an operator to determine
# its precedence.  We don't care about checking for conflicts...
def precedence(range):
    (lo, hi) = range
    return (lo + hi) // 2

class GExpression(Rule):
    def __init__(self, level):
        self.level = level

    def parse(self, s):
        if s == []:
            return parseError(["GExpression: empty list"], s)

        # If at the top precedence level, get a basic expression.
        if self.level == 18:
            return self.match("GExpression18", s, GBasicExpression(), True)

        # See if this is an expression starting with /\ or \/
        lex = lexeme(s[0])
        if lex in { "/\\", "\\/" }:
            (lex, line, column, first) = s[0]
            token = (lex, column, True)
            stack.append(token)
            (t, a, r) = GExpression(0).parse(s[1:])
            if t == False:
                stack.pop()
                return parseError([ ("GExpression" + str(self.level), s[0]) ] + a, r)

            while r != [] and junct(r[0]) == token:
                (t2, a2, r2) = GExpression(0).parse(r[1:])
                if not t2:
                    stack.pop()
                    return parseError([ "GExpression0" ] + a2, r2)
                (t, a, r) = ("Infix0", (s[0], (t, a), (t2, a2)), r2)
            stack.pop()
            return (t, a, r)

        # See if the expression starts with a prefix operator.
        # TODO.  Should match again GGeneralPrefixOp
        x = PrefixOps.get(lexeme(s[0]))
        if x != None:
            # Compute the precedence level of the operator.
            prec = precedence(x)

            # Parse an expression of the given precedence level.
            (t, a, r) = GExpression(prec).parse(s[1:])
            if t == False:
                return parseError([ "GExpression" + str(self.level)
                                            + ": " + str(s[0]) ] + a, r)
            (t, a, r) = ("Prefix" + str(prec), (s[0], (t, a)), r)

        # If not a prefix get an expression at the next precedence level
        else:
            (t, a, r) = GExpression(self.level + 1).parse(s)
            if t == False:
                return parseError([ "GExpression" + str(self.level)
                                            + ": " + str(s[0]) ] + a, r)

        # Loop through the remainder.
        while r != []:
            # If a disjunct or conjunct, we're done.
            if junct(r[0]) in stack:
                return (t, a, r)

            # See if it's a postfix expression with sufficient precedence
            x = PostfixOps.get(lexeme(r[0]))
            if x != None:
                # Compute the precedence level.  If of a lower level, we're done.
                prec = precedence(x)
                if prec <= self.level:
                    return (t, a, r)

                # Check for an index expression
                if lexeme(r[0]) == '[':
                    (t2, a2, r2) = Concat([tok("["),
                            CommaList(GExpression(0)), tok("]")]).parse(r)
                    if not t2:
                        return (False, ["GExpresssion" + str(self.level)
                                            + ": bad index"] + a2, r2)
                    (t, a, r) = ("Index", (r[0], (t, a), a2[1]), r2)
                else:
                    (t, a, r) = ("Postfix" + str(self.level), ((t, a),
                                            r[0]), r[1:])

            else:
                # See if the next token is an infix operator.  If not, we're done.
                lex = lexeme(r[0])
                x = InfixOps.get(lex)
                if x == None:
                    return (t, a, r)

                # If it's the '.' operator, it should be followed by a field name
                if lex == ".":
                    (t2, a2, r2) = Name().parse(r[1:])
                    if t2 == False:
                        return (False, [ "GExpression" + str(self.level)
                                            + ": no field name" ] + a2, r2)
                    assert t2 == "Name"
                    (t, a, r) = ("Index", (r[0], (t, a),
                        ("CommaList", [("String", '"' + lexeme(a2) + '"')])), r2)

                else:
                    # Compute the precedence.  If too low, we're done.
                    prec = precedence(x)
                    if prec <= self.level:
                        return (t, a, r)

                    # Get the next expression at that precedence level.
                    (t2, a2, r2) = GExpression(prec).parse(r[1:])
                    if t2 == False:
                        return (False, [ "GExpression" + str(self.level)
                                            + ": " + str(r[0]) ] + a2, r2)

                    # Cartesian products are not infix operators
                    if lex in { "\\X", "\\times" }:
                        if t == "Cartesian":
                            (t, a, r) = ("Cartesian", a + [(t2, a2)], r2)
                        else:
                            (t, a, r) = ("Cartesian", [(t, a), (t2, a2)], r2)
                    else:
                        (t, a, r) = ("Infix" + str(self.level),
                                            (r[0], (t, a), (t2, a2)), r2)
        return (t, a, r)

# Separate AST node for the EXCEPT clause in a function update operation
class GExcept(Rule):
    def parse(self, s):
        (t, a, r) = CommaList(Concat([
                tok("!"),
                AtLeast(OneOf([
                    Tag("efield", Concat([ tok("."), Name() ]), [1]),
                    Tag("elist", Concat([ tok("["), CommaList(GExpression(0)),
                                                    tok("]"), ]), [1])
                ]), 1),
                tok("="),
                GExpression(0)
            ])).parse(s)
        if not t:
            return (False, ["GExcept"] + a, r)
        assert t == "CommaList"
        result = []
        for x in a:
            (t2, a2) = x
            assert t2 == "Concat"
            (t3, a3) = a2[1]
            assert t3 == "AtLeast1"
            result = result + [ (a3, a2[3]) ]
        return ("GExcept", result, r)

class GBasicExpression(Rule):
    def parse(self, s):
        return self.match("GBasicExpression", s, OneOf([
            Tag("op", Concat([
                GGeneralIdentifier(), Optional(Concat([
                    tok("("), CommaList(GArgument()), tok(")") ]), [1])
            ]), [0, 1]),

            Tag("parentheses", Concat([
                            tok("("), GExpression(0), tok(")") ]), [1]),

            Tag("exists", Concat([ tok("\\E"), CommaList(GQuantifierBound()),
                                    tok(":"), GExpression(0) ]), [1, 3]),

            Tag("forall", Concat([ tok("\\A"), CommaList(GQuantifierBound()),
                                    tok(":"), GExpression(0) ]), [1, 3]),

            Tag("temporal_exists", Concat([ tok("\\EE"), CommaList(Identifier()),
                                    tok(":"), GExpression(0) ]), [1, 3]),

            Tag("temporal_forall", Concat([ tok("\\AA"), CommaList(Identifier()),
                                    tok(":"), GExpression(0) ]), [1, 3]),

            Tuple(),

            Tag("set", Concat([ tok("{"), Optional(CommaList(GExpression(0))),
                                    tok("}") ]), [1]),

            Tag("filter", Concat([ tok("{"), IdentifierOrTuple(),
                                    tok("\\in"), GExpression(0),
                                    tok(":"), GExpression(0),
                                    tok("}") ]), [1, 3, 5]),

            Tag("gen", Concat([ tok("{"), GExpression(0), tok(":"),
                                    CommaList(GQuantifierBound()),
                                    tok("}") ]), [1, 3]),

            Tag("square", Concat([ tok("["), GExpression(0), tok("]_"),
                                    GExpression(0) ]), [1, 3]),

            Tag("lambda", Concat([
                tok("["), CommaList(GQuantifierBound()), tok("|->"),
                                    GExpression(0), tok("]")
            ]), [1, 3]),

            Tag("except", Concat([ tok("["), GExpression(0), tok("EXCEPT"),
                                    GExcept(), tok("]") ]), [1, 3]),

            Tag("funcset", Concat([
                tok("["), GExpression(0), tok("->"), GExpression(0), tok("]")
            ]), [1, 3]),

            Tag("recorddef", Concat([
                tok("["),
                CommaList(Concat([ Name(), tok(":"), GExpression(0) ])),
                tok("]")
            ]), [1]),

            Tag("recordvalue", Concat([
                tok("["),
                CommaList(Concat([ Name(), tok("|->"), GExpression(0) ])),
                tok("]")
            ]), [1]),

            Tag("choose", Concat([
                tok("CHOOSE"), Identifier(),
                Optional(Concat([tok("\\in"), GExpression(0)]), [1]),
                tok(":"), GExpression(0) ]), [1, 2, 4]),

            Tag("if", Concat([ tok("IF"), GExpression(0), tok("THEN"),
                    GExpression(0), tok("ELSE"), GExpression(0) ]), [1, 3, 5]),

            Tag("case", Concat([ tok("CASE"), SeparatorList(
                    Concat([ GExpression(0), tok("->"), GExpression(0) ]),
                    "[]", False), Optional(
                    Concat([ tok("[]"), tok("OTHER"), tok("->"), GExpression(0) ]),
                    [3]) ]), [1, 2]),

            Tag("let", Concat([ tok("LET"),
                AtLeast( OneOf([
                    GOperatorDefinition(),
                    GFunctionDefinition(),
                    GModuleDefinition() ]), 1),
                tok("IN"), GExpression(0) ]), [1, 3]),

            # There's an ambiguity for WF_a(b): does it mean
            # "WF_ a(b)" or "WF_a (b)"?  My parser gets confused
            # so I restricted it a bit
            Tag("wf", Concat([ tok("WF_"), IdentifierOrTuple(),
                    tok("("), GExpression(0), tok(")")]), [1, 3]),

            Tag("sf", Concat([ tok("SF_"), IdentifierOrTuple(),
                    tok("("), GExpression(0), tok(")")]), [1, 3]),

            Number(),

            String(),

            Tag("at", tok("@"))
        ]))

#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 
####    Compiler: Lexer
#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 

# Initial list of tokens for the lexer.  More added later from op tables.
tokens = [
    "<<", ">>", "]_", "<-", "->", "|->", "==",
    "\\A", "\\E", "\\AA", "\\EE", "WF_", "SF_"
]

# Add tokens from the given operator table
def addTokens(boundedvars):
    global tokens
    for (op, (low, hi)) in boundedvars.items():
        if not isalnum(op[0]) and not (len(op) > 1 \
                                and op[0] == "\\" and isletter(op[1])):
            tokens = tokens + [ op ]

# add tokens from the operators
addTokens(PrefixOps)
addTokens(InfixOps)
addTokens(PostfixOps)

def stringToken(x):
    (lexeme, where, column, first) = x
    (file, line) = where
    return lexeme + " (" + file + ":" + str(line) + ":" + str(column) + ")"

# Turn input into a sequence of tokens.  Each token is a tuple
#   (lexeme, (file, line), column, first), where first is true if
#   it's the first token on the line
def lexer(s, file):
    result = []
    line = 1
    column = 1
    first = True
    while s != "":
        # see if it's a blank
        if s[0] in { " ", "\t" }:
            s = s[1:]
            column += 1
            continue

        if s[0] == "\n":
            s = s[1:]
            line += 1
            column = 1
            first = True
            continue

        # Skip over "pure" TLA+
        if s.startswith("\\*++:SPEC"):
            s = s[8:]
            while len(s) > 0 and not s.startswith("\\*++:PlusPy"):
                s = s[1:]
            continue

        # skip over line comments
        if s.startswith("\\*"):
            s = s[2:]
            while len(s) > 0 and s[0] != '\n':
                s = s[1:]
            continue

        # skip over nested comments
        if s.startswith("(*"):
            count = 1
            s = s[2:]
            column += 2
            while count != 0 and s != "":
                if s.startswith("(*"):
                    count += 1
                    s = s[2:]
                    column += 2
                elif s.startswith("*)"):
                    count -= 1
                    s = s[2:]
                    column += 2
                elif s[0] == "\n":
                    s = s[1:]
                    line += 1
                    column = 1
                    first = True
                else:
                    s = s[1:]
                    column += 1
            continue

        # a series of four or more '-' characters is a lexeme
        if s.startswith("----"):
            s = s[4:]
            c = column
            column += 4
            while len(s) > 0 and s[0] == '-':
                s = s[1:]
                column += 1
            result += [ ("----", (file, line), c, first) ]
            first = False
            continue

        # a series of four or more '=' characters is a lexeme
        if s.startswith("===="):
            s = s[4:]
            c = column
            column += 4
            while len(s) > 0 and s[0] == '=':
                s = s[1:]
                column += 1
            result += [ ("====", (file, line), c, first) ]
            first = False
            continue

        # if a backslash, it may be an special operator.  Otherwise just \
        if s[0] == "\\" and len(s) > 1 and isalnum(s[1]):
            i = 2
            while i < len(s) and isalnum(s[i]):
                i += 1
            result += [ (s[:i], (file, line), column, False) ]
            first = False
            s = s[i:]
            column += i
            continue

        # see if it's a multi-character token.  Match with the longest one
        found = ""
        for t in tokens:
            if s.startswith(t) and len(t) > len(found):
                found = t
        if found != "":
            result += [ (found, (file, line), column, first) ]
            first = False
            s = s[len(found):]
            column += len(found)
            continue

        # see if a sequence of letters and numbers
        if isnamechar(s[0]):
            i = 0
            while i < len(s) and isnamechar(s[i]):
                i += 1
            result += [ (s[:i], (file, line), column, first) ]
            first= False
            s = s[i:]
            column += i
            continue

        # string
        if s[0] == '"':
            i = 1
            str = '"'
            while i < len(s) and s[i] != '"':
                if s[i] == '\\':
                    i += 1
                    if i == len(s):
                        break
                    if s[i] == '"':
                        str += '"'
                    elif s[i] == '\\':
                        str += '\\'
                    elif s[i] == 't':
                        str += '\t'
                    elif s[i] == 'n':
                        str += '\n'
                    elif s[i] == 'f':
                        str += '\f'
                    elif s[i] == 'r':
                        str += '\r'
                    else:
                        str += s[i]
                else:
                    str += s[i]
                i += 1
            if i < len(s):
                i += 1
            str += '"'
            result += [ (str, (file, line), column, first) ]
            first = False
            s = s[i:]
            column += i
            continue

        # everything else is a single character token
        result += [ (s[0], (file, line), column, first) ]
        first = False
        s = s[1:]
        column += 1
    return result

#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 
####    Compiler: Expressions
#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 

# Get the prefix of an A!B!C type expression
def getprefix(ast, operators):
    (t, a) = ast
    assert t == "GInstancePrefix"
    (t1, a1) = a
    assert t1 == "AtLeast0"
    instances = []
    for x in a1:
        (t2, a2) = x
        assert t2 == "Concat"
        assert len(a2) == 3
        (t3, a3) = a2[0]
        assert t3 == "Identifier"
        od = operators[lexeme(a3)]
        assert isinstance(od, OperatorExpression)
        if not isinstance(od.expr, ModInst):
            print("trying to instantiate", od.expr)
        assert isinstance(od.expr, ModInst)
        (t4, a4) = a2[1]
        assert t4 == "Optional"
        args = []
        if a4 != None:
            (t5, a5) = a4
            assert t5 == "CommaList"
            for (t, a) in a5:
                assert t == "GArgument"
                args += [ compileExpression(a) ]
        instances += [(a3, od, args)]
        operators = od.expr.operators
    return (operators, instances)

# handle complicated situations like A(a)!B(b)!C(c)
# This is best done backwards:
#   First find A!B!C
#   Make substitutions to create A!B!C(c)
#   Then A!B(b)!C(c)
#   Finally A(a)!B(b)!C(c)
def opSubst(instances):
    (lex, iop, iargs) = instances[0]
    assert isinstance(iop, OperatorExpression)
    oargs = iop.args
    oexpr = iop.expr

    if len(instances) == 1:
        expr = oexpr
    else:
        assert isinstance(oexpr, ModInst)
        expr = opSubst(instances[1:])

    # A 1st or 2nd order operator has arguments.  However, when passed as
    # an argument to another operator no arguments are specified.  In that
    # case it should not be expanded here.
    if len(oargs) > 0 and iargs == []:
        return iop

    # Check that the arity of the operator is correct
    if (len(oargs) != len(iargs)):
        print("arity mismatch", lex, "expected:", len(oargs), "got:", len(iargs))
        exit(1)

    # Do a substitution, replacing argument names with argument values
    subs = {}
    for i in range(len(oargs)):
        subs[oargs[i]] = iargs[i]

    x = expr.substitute(subs)
    if isinstance(x, BuiltinExpression):
        return BuiltinExpression(id=x.id, args=x.args,
                    wrapper=x.wrapper, lex=lex, primed=x.primed)
    return x

# This is an expression of the form A!B(b)!C, say
def compileOpExpression(od):
    primed = False

    # print("COE", od)
    (t0, a0) = od[0]
    assert t0 in [ "GGeneralIdentifier", "GGeneralPrefixOp",
                        "GGeneralInfixOp", "GGeneralPostfixOp" ]
    assert len(a0) == 2

    (t1, a1) = a0
    assert t1 == "Concat"
    assert len(a1) == 2

    # get the list of instances in the prefix
    (operators, instances) = getprefix(a1[0], modstk[-1].operators)

    # get the identifier and arguments
    # print("COE1", a1[1])
    (t2, a2) = a1[1]
    assert t2 in {"Identifier", "Tok"}
    name = lexeme(a2)
    (t3, a3) = od[1]
    assert t3 == "Optional"
    if a3 == None:
        args = []
    else:
        (t4, a4) = a3
        assert t4 == "CommaList"
        args = a4

    cargs = []
    for (t, a) in args:
        assert t == "GArgument"
        comp = compileExpression(a)
        if comp.primed:
            primed = True
        cargs = cargs + [comp]

    # We are now at a point where we have to figure out whether this
    # is the name of an operator or another identifier such as a
    # variable.  If there was a prefix or there are arguments, it must
    # be the name of an operator.  If not, it could be either.
    id = name_lookup(name)
    # print("OE", name, id, cargs, operators.get(id))
    if id and not isinstance(id, OperatorExpression):
        assert instances == []
        if cargs == []:
            return id
        if isinstance(id, ConstantExpression):
            assert id.count == len(cargs)
            return ParameterExpression(id, cargs)
        else:
            assert isinstance(id, ArgumentExpression)
            assert id.nargs == len(cargs)
            return ParameterExpression(id, cargs)
    elif operators.get(name) == None:
        print("unknown identifier", stringToken(a2))
        exit(1)
    else:
        id = operators[name]

    assert isinstance(id, OperatorExpression)
    return opSubst(instances + [(a2, id, cargs)])

def compileQuantBoundExpression(which, qs, ex):
    quantifiers = []
    domains = []
    (t, a) = qs
    assert t == "CommaList"     # one or more quantifiers
    assert len(a) > 0
    for q in a:                 # loop through these
        (t2, a2) = q
        assert t2 == "GQuantifierBound"
        domain = compileExpression(a2[1])
        (t3, a3) = a2[0]
        assert t3 in {"CommaList", "Tuple"}
        assert t3 == "CommaList"            # ignore tuples for now
        for (t4, a4) in a3:
            assert t4 == "Identifier"
            quantifiers += [BoundvarExpression(lexeme(a4))]
            domains += [domain]

    name_stack.append({ bv.id:bv for bv in quantifiers })
    expr = compileExpression(ex)
    name_stack.pop()

    if which == "exists":
        return ExistsExpression(quantifiers=quantifiers, domains=domains, expr=expr, primed=expr.primed)
    if which == "forall":
        return ForallExpression(quantifiers=quantifiers, domains=domains, expr=expr, primed=expr.primed)
    if which == "lambda":
        return LambdaExpression(quantifiers=quantifiers, domains=domains, expr=expr, primed=expr.primed)
    if which == "gen":
        return GenExpression(expr=expr, quantifiers=quantifiers, domains=domains, primed=expr.primed)
    assert False

def compileQuantUnboundExpression(which, func):
    quantifiers = []
    (t, a) = func[0]
    assert t == "CommaList"     # one or more quantifiers
    assert len(a) > 0
    for q in a:                 # loop through these
        (t2, a2) = q
        assert t2 == "Identifier"
        quantifiers += [VariableExpression(lexeme(a2))]

    name_stack.append({ bv.id:bv for bv in quantifiers })
    expr = compileExpression(func[1])
    name_stack.pop()

    if which == "temporal_exists":
        return Temporal_existsExpression(quantifiers=quantifiers, expr=expr, primed=expr.primed)
    if which == "temporal_forall":
        return Temporal_forallExpression(quantifiers=quantifiers, expr=expr, primed=expr.primed)
    assert False

def compileExpression(ast):
    (t, a) = ast
    if t == False:
        print("compileExpression", a)
        assert False
    elif t == "op":
        return compileOpExpression(a)
    elif t in { "arg-prefix", "arg-infix", "arg-postfix" }:
        return compileOpExpression([a, ("Optional", None)])
    elif t in { "exists", "forall", "lambda" }:
        return compileQuantBoundExpression(t, a[0], a[1])
    elif t == "gen":
        return compileQuantBoundExpression(t, a[1], a[0])
    elif t in { "temporal_exists", "temporal_forall" }:
        return compileQuantUnboundExpression(t, a)
    elif t in { "GBasicExpression", "parentheses" }:
        return compileExpression(a)
    elif t == "Tuple":
        return TupleExpression().fromAST(a)
    elif t == "set":
        return SetExpression().fromAST(a)
    elif t == "filter":
        return FilterExpression().fromAST(a)
    elif t == "Number":
        return NumberExpression(a)
    elif t == "String":
        return StringExpression(a[1:-1])
    elif t == "Index":
        return IndexExpression().fromAST(a)
    elif t.startswith("Prefix"):
        return OutfixExpression().fromAST(a)
    elif t.startswith("Postfix"):
        (expr, op) = a
        if lexeme(op) == "'":
            return PrimeExpression().fromAST(expr)
        else:
            return OutfixExpression().fromAST(a)
    elif t.startswith("Infix"):
        return InfixExpression().fromAST(a)
    elif t == "Cartesian":
        return CartesianExpression().fromAST(a)
    elif t == "choose":
        return ChooseExpression().fromAST(a)
    elif t == "if":
        return IfExpression().fromAST(a)
    elif t == "case":
        return CaseExpression().fromAST(a)
    elif t == "let":
        return LetExpression().fromAST(a)
    elif t == "recordvalue":
        return RecordvalueExpression().fromAST(a)
    elif t == "funcset":
        return FuncsetExpression().fromAST(a)
    elif t == "except":
        return ExceptExpression().fromAST(a)
    elif t == "square":
        return SquareExpression().fromAST(a)
    elif t == "recorddef":
        return RecorddefExpression().fromAST(a)
    elif t in { "wf", "sf" }:
        return FairnessExpression(t, a)
    elif t == "at":
        return name_find("@")
    else:
        print("Can't compile ", ast)
        return None

# handle an "Operator(args) == Expression" definition
def compileOperatorDefinition(od):
    (t0, a0) = od[0]
    if t0 == "GNonFixLHS":
        assert len(a0) == 2
        (t2, a2) = a0[0]
        assert t2 == "Identifier"
        id = lexeme(a2)
        (t3, a3) = a0[1]
        assert t3 == "Optional"
        if a3 == None:
            args = []
        else:
            (t4, a4) = a3
            assert t4 == "CommaList"
            args = a4

        cargs = []
        for (t, a) in args:
            assert t == "GOpDecl"
            (t2, a2) = a
            if t2 == "Identifier":
                cargs = cargs + [(lexeme(a2), 0)]
            elif t2 == "paramOp":
                (t3, a3) = a2[0]
                assert t3 == "Identifier"
                (t4, a4) = a2[1]
                assert t4 == "CommaList"
                cargs = cargs + [(lexeme(a3), len(a4))]
            elif t2 == "prefixOp" or t2 == "postfixOp":
                cargs = cargs + [(a2, 1)]
            elif t2 == "infixOp":
                cargs = cargs + [(a2, 2)]
            else:
                assert False
    elif t0 == "prefix":
        (t1, a1) = a0
        assert t1 == "Concat"
        (t3, a3) = a1[0]
        assert t3 == "Tok"
        (t4, a4) = a1[1]
        assert t4 == "Identifier"
        id = lexeme(a3)
        cargs = [(lexeme(a4), 0)]
    elif t0 == "infix":
        (t1, a1) = a0
        assert t1 == "Concat"
        (t2, a2) = a1[0]
        assert t2 == "Identifier"
        (t3, a3) = a1[1]
        assert t3 == "Tok"
        (t4, a4) = a1[2]
        assert t4 == "Identifier"
        id = lexeme(a3)
        cargs = [(lexeme(a2), 0), (lexeme(a4), 0)]
    elif t0 == "postfix":
        (t1, a1) = a0
        assert t1 == "Concat"
        (t2, a2) = a1[0]
        assert t2 == "Identifier"
        (t3, a3) = a1[1]
        assert t3 == "Tok"
        id = lexeme(a3)
        cargs = [(lexeme(a2), 0)]
    else:
        print("compileOperatorDefinition", t0, a0)
        assert False

    # print("OD", modstk[-1].name, id)
    args = [ArgumentExpression(a, n) for (a, n) in cargs]
    name_stack.append({ a.id:a for a in args })
    ce = compileExpression(od[1])
    name_stack.pop()

    return (id, args, ce)

# handle a "Function[args] == Expression" definition.  Define as
#   f[x \in D] == e  ==>   f == CHOOSE f: f = [x \ D: e]
def compileFunctionDefinition(od):
    (t0, a0) = od[0]
    assert t0 == "Identifier"
    id = lexeme(a0)
    bve = BoundvarExpression(id)
    name_stack.append({ id: bve })
    f = compileQuantBoundExpression("lambda", od[1], od[2])
    name_stack.pop()
    (op, file, column, first) = a0
    infix = InfixExpression(op=("=", file, column, first), lhs=bve, rhs=f)
    c = ChooseExpression(id=bve, expr=infix)
    return (id, [], c)

# Convert a value to something a little more normal and better for printing
def convert(v):
    if isinstance(v, tuple):
        return tuple([ convert(x) for x in v ])
    if isinstance(v, frozenset):
        return [ convert(y) for y in set(v) ]
    if isinstance(v, FrozenDict):
        return { convert(x):convert(y) for (x, y) in v.d.items() }
    return v

def is_tla_id(s):
    if not isinstance(s, str):
        return False
    if any(not isnamechar(c) for c in s):
        return False
    return any(isletter(c) for c in s)

# Defines a sorting order on all values
def key(v):
    if isinstance(v, bool):
        return (0, v)
    if isinstance(v, int):
        return (1, v)
    if isinstance(v, str):
        return (2, v)
    if isinstance(v, tuple):
        return (3, [key(x) for x in v])
    if isinstance(v, frozenset):
        lst = [key(x) for x in v]
        return (4, sorted(lst))
    if isinstance(v, FrozenDict):
        lst = [(key(k), key(v)) for (k, v) in v.d.items()]
        return (5, sorted(lst))
    if isinstance(v, Nonce):
        return (6, v.id)
    print(v)
    assert False

# Convert a value to a string in TLA+ format
def format(v):
    if v == "":
        return "<<>>"
    if v == frozenset():
        return "{}"
    if isinstance(v, bool):
        return "TRUE" if v else "FALSE"
    if isinstance(v, str):
        return '"' + v + '"'
    if isinstance(v, tuple):
        result = ""
        for x in v:
            if result != "":
                result += ", "
            result += format(x)
        return "<< " + result + " >>"
    if isinstance(v, frozenset):
        lst = sorted(v, key=lambda x: key(x))
        result = ""
        for x in lst:
            if result != "":
                result += ", "
            result += format(x)
        return "{ " + result + " }"
    if isinstance(v, FrozenDict):
        return v.format()
    return str(v)

class Expression:
    def __init__(self):
        self.primed = None        # set if this expression is primed

    def __repr__(self):
        return self.__str__()

    def runInit(self, containers, boundedvars):
        print("runInit", self)
        assert False

    def eval(self, containers, boundedvars):
        print("Eval: ", self)
        assert False

    def apply(self, containers, boundedvars, fargs):
        v = self.eval(containers, boundedvars)
        if v == None:
            print("Default apply", self, fargs)
        assert v != None
        return funceval(v, fargs)

# A built-in expression
class BuiltinExpression(Expression):
    def __init__(self, id=None, args=None, wrapper=None, lex=None, primed=False):
        self.id = id
        self.args = args
        self.wrapper = wrapper
        self.lex = lex
        self.primed = primed

    def __str__(self):
        return "Builtin(" + self.id + ", " + str(self.args) + ", " + \
                    str(self.wrapper) + ", " + str(self.lex) + ")"

    def substitute(self, subs):
        args = [x.substitute(subs) for x in self.args]
        return BuiltinExpression(id=self.id, args=args,
                    wrapper=self.wrapper, lex=self.lex, primed=self.primed)

    def eval(self, containers, boundedvars):
        # print("BI eval", self)
        args = [ arg.eval(containers, boundedvars) for arg in self.args ]
        try:
            return self.wrapper.eval(self.id, args)
        except Exception as e:
            print("Evaluating", stringToken(self.lex), "failed")
            print(e)
            print(traceback.format_exc())
            exit(1);

# The simplest of expressions is just a value
class ValueExpression(Expression):
    def __init__(self, value=None, primed=False):
        self.value = value
        self.primed = primed

    def __str__(self):
        return "Value(" + str(self.value) + ")"

    def substitute(self, subs):
        return self

    def eval(self, containers, boundedvars):
        return self.value

# Another simple one is a variable expression
class VariableExpression(Expression):
    def __init__(self, id=None, primed=False):
        self.id = id
        self.primed = primed

    def __str__(self):
        return "Variable(" + str(self.id) + ")"

    def substitute(self, subs):
        if subs.get(self) == None:
            return self
        else:
            global initializing
            if initializing:
                return PrimeExpression(expr=subs[self])
            else:
                return subs[self]

    def eval(self, containers, boundedvars):
        print("Error: variable", self.id, "not realized", containers, boundedvars)
        exit(1)

# Another simple one is a constant expression
class ConstantExpression(Expression):
    def __init__(self, id=None, count=0, primed=False):
        self.id = id
        self.count = count
        self.primed = primed

    def __str__(self):
        return "Constant(" + self.id + ", " + str(self.count) + ")"

    def substitute(self, subs):
        if subs.get(self) == None:
            return self
        else:
            return subs[self]

    def eval(self, containers, boundedvars):
        print("Error: constant", self.id, "does not have a value")
        exit(1)

# Another simple one is a bounded variable (in \E, lambdas, etc.)
# The values are in the "boundedvars" dictionary
class BoundvarExpression(Expression):
    def __init__(self, id=None, primed=False):
        self.id = id
        self.primed = primed

        global bv_counter
        bv_counter += 1
        self.uid = bv_counter

    def __str__(self):
        return "Boundvar(" + str(self.id) + ", " + str(self.uid) + ")"

    def substitute(self, subs):
        return self

    def eval(self, containers, boundedvars):
        expr = boundedvars[self]
        assert isinstance(expr, ValueExpression)
        return expr.eval(containers, boundedvars)

    def apply(self, containers, boundedvars, fargs):
        expr = boundedvars[self]
        return expr.apply(containers, boundedvars, fargs)

# An "argument" is the usage of an argument to an operator definition
# inside its body.  It itself may have arguments.  Needs to be substituted
# before evaluation
class ArgumentExpression(Expression):
    def __init__(self, id=None, nargs=0, primed=False):
        self.id = id
        self.nargs = nargs
        self.primed = primed

    def __str__(self):
        return "Argument(" + str(self.id) + ", " + str(self.nargs) + ")"

    def substitute(self, subs):
        if subs.get(self) == None:
            return self
        else:
            return subs[self]

    def eval(self, containers, boundedvars):
        print("Error: argument", self.id, "not realized", self.nargs, containers, boundedvars)
        assert False

# This is like an ArgumentExpression with arguments of its own (i.e., an
# argument of a 2nd order operator, but with its arguments instantiated
# It still needs to be substituted with an actual operator before evaluation
class ParameterExpression(Expression):
    def __init__(self, argument=None, args=None, primed=False):
        self.argument = argument
        self.args = args
        self.primed = primed

    def __str__(self):
        return "Parameter(" + str(self.argument) + ", " + str(self.args) + ")"

    def substitute(self, subs):
        if subs.get(self.argument):
            op = subs.get(self.argument)
            if isinstance(op, OperatorExpression):
                assert isinstance(op, OperatorExpression)
                assert len(self.args) == len(op.args)
                s = subs.copy()
                for i in range(len(self.args)):
                    s[op.args[i]] = self.args[i].substitute(s)
                return op.expr.substitute(s)
            else:
                assert isinstance(op, ArgumentExpression)
                assert len(self.args) == op.nargs
                # print("ZZZ", self, op, subs)
                return ParameterExpression(argument=op, args=self.args,
                                            primed=self.primed)
        else:
            args = [a.substitute(subs) for a in self.args]
            return ParameterExpression(argument=self.argument, args=args,
                                            primed=self.primed)

    def eval(self, containers, boundedvars):
        print("Error: parameter", self.argument, "not realized")
        assert False

class OperatorExpression(Expression):
    def __init__(self, id=None, args=None, expr=None, primed=False):
        self.id = id
        self.args = args
        self.expr = expr
        self.primed = primed

    def __str__(self):
        return "Operator(" + self.id + ", " + str(self.args) + ")"
            # + ", " + self.expr.__str__() \

    def substitute(self, subs):
        return OperatorExpression(id=self.id, args=self.args,
                    expr=self.expr.substitute(subs), primed=self.primed)

    def eval(self, containers, boundedvars):
        # print("operator", self, "invoked without arguments")
        return self

# Another simple one is a container expression, which holds a value for a variable
# for both the previous state and the next state
class ContainerExpression(Expression):
    def __init__(self, var=None, primed=False):
        self.var = var
        self.primed = primed
        self.prev = None
        self.next = None

    def __str__(self):
        return "Container(" + self.var.id + ", " + str(convert(self.prev)) \
                            + ", " + str(convert(self.next)) + ")"

    def substitute(self, subs):
        return self

    def eval(self, containers, boundedvars):
        if self.prev == None:
            print("null container", self)
        assert self.prev != None
        return self.prev

class SquareExpression(Expression):
    def __init__(self, lhs=None, rhs=None, primed=False):
        self.lhs = lhs
        self.rhs = rhs
        self.primed = primed

    def fromAST(self, exprs):
        assert len(exprs) == 2
        self.lhs = compileExpression(exprs[0])
        self.rhs = compileExpression(exprs[1])
        assert not self.rhs.primed
        self.primed = self.lhs.primed
        return self

    def __str__(self):
        return "Square(" + self.lhs.__str__() + ", " + self.rhs.__str__() + ")"

    def substitute(self, subs):
        lhs = self.lhs.substitute(subs)
        rhs = self.rhs.substitute(subs)
        return SquareExpression(lhs=lhs, rhs=rhs, primed=self.primed)

    def eval(self, containers, boundedvars):
        return self.lhs.eval(containers, boundedvars)

class FairnessExpression(Expression):
    def __init__(self, t, a):
        self.type = t
        (t0, a0) = a[0]
        if t0 == "Identifier":
            self.lhs = VariableExpression(id=lexeme(a0))
        else:
            self.lhs = compileExpression(a[0])
        self.rhs = compileExpression(a[1])
        assert not self.lhs.primed
        self.primed = self.rhs.primed

    def __str__(self):
        return "FAIRNESS(" + self.type + ", " + self.lhs.__str__() \
                    + ", " +  self.rhs.__str__() + ")"

    def substitute(self, subs):
        return self

class LambdaExpression(Expression):
    def __init__(self, quantifiers=None, domains=None, expr=None, primed=False):
        self.quantifiers = quantifiers
        self.domains = domains
        self.expr = expr
        self.primed = primed

    def __str__(self):
        return "Lambda(" + str(self.quantifiers) + ", " + self.expr.__str__() + ")"

    def substitute(self, subs):
        domains = [ expr.substitute(subs) for expr in self.domains ]
        expr = self.expr.substitute(subs)
        return LambdaExpression(quantifiers=self.quantifiers, domains=domains,
                            expr=expr, primed=self.primed)

    def enumerate(self, containers, domains, lst, result, boundedvars):
        if domains == []:
            if len(lst) == 1:
                result[lst[0]] = self.expr.eval(containers, boundedvars)
            else:
                result[tuple(lst)] = self.expr.eval(containers, boundedvars)
        else:
            (var, domain) = domains[0]
            if domain == False:
                print("Error: possibly trying to evaluate Nat")
                exit(1)
            domain = sorted(domain, key=lambda x: key(x))
            for val in domain:
                boundedvars[var] = ValueExpression(val)
                self.enumerate(containers, domains[1:], lst + [val],
                                        result, boundedvars)

    def eval(self, containers, boundedvars):
        domains = []
        for i in range(len(self.quantifiers)):
            domains += [ (self.quantifiers[i],
                            self.domains[i].eval(containers, boundedvars)) ]
        result = {}
        self.enumerate(containers, domains, [], result, boundedvars.copy())
        return simplify(FrozenDict(result))

    def apply(self, containers, boundedvars, fargs):
        assert len(self.quantifiers) == len(fargs)
        bv = boundedvars.copy()
        for i in range(len(fargs)):
            var = self.quantifiers[i]
            bv[var] = ValueExpression(fargs[i])
        return self.expr.eval(containers, bv)

class ExistsExpression(Expression):
    def __init__(self, quantifiers=None, domains=None, expr=None, primed=False):
        self.quantifiers = quantifiers
        self.domains = domains
        self.expr = expr
        self.primed = primed

    def __str__(self):
        return "Exists(" + str(self.quantifiers) + ", " + self.expr.__str__() + ")"

    def substitute(self, subs):
        domains = [ expr.substitute(subs) for expr in self.domains ]
        expr = self.expr.substitute(subs)
        return ExistsExpression(quantifiers=self.quantifiers, domains=domains,
                            expr=expr, primed=self.primed)

    def enumerate(self, containers, domains, boundedvars):
        global IO_outputs

        if domains == []:
            return self.expr.eval(containers, boundedvars)
        (var, domain) = domains[0]

        # Pseudo-randomized SAT solving...
        domain = sorted(domain, key=lambda x: key(x))
        domain = random.sample(list(domain), len(domain))

        # Copy next state in case need to restore
        output_copy = IO_outputs.copy()
        copy = {}
        for (k, v) in containers.items():
            copy[k] = v.next
        for val in domain:
            boundedvars[var] = ValueExpression(val)
            if self.enumerate(containers, domains[1:], boundedvars):
                return True
            # restore state before trying next
            for (k, v) in copy.items():
                containers[k].next = v
            IO_outputs = output_copy
        return False

    def eval(self, containers, boundedvars):
        domains = []
        for i in range(len(self.quantifiers)):
            domains += [ (self.quantifiers[i],
                            self.domains[i].eval(containers, boundedvars)) ]
        return self.enumerate(containers, domains, boundedvars.copy())

class ForallExpression(Expression):
    def __init__(self, quantifiers=None, domains=None, expr=None, primed=False):
        self.quantifiers = quantifiers
        self.domains = domains
        self.expr = expr
        self.primed = primed

    def __str__(self):
        return "Forall(" + str(self.quantifiers) + ", " + self.expr.__str__() + ")"

    def substitute(self, subs):
        domains = [ expr.substitute(subs) for expr in self.domains ]
        expr = self.expr.substitute(subs)
        return ForallExpression(quantifiers=self.quantifiers, domains=domains,
                            expr=expr, primed=self.primed)

    def enumerate(self, containers, domains, boundedvars):
        if domains == []:
            return self.expr.eval(containers, boundedvars)
        (var, domain) = domains[0]
        domain = sorted(domain, key=lambda x: key(x))
        for val in domain:
            boundedvars[var] = ValueExpression(val)
            if not self.enumerate(containers, domains[1:], boundedvars):
                return False
        return True

    # TODO.  This may not work for primed expressions currently
    def eval(self, containers, boundedvars):
        domains = []
        for i in range(len(self.quantifiers)):
            domains += [ (self.quantifiers[i],
                            self.domains[i].eval(containers, boundedvars)) ]
        return self.enumerate(containers, domains, boundedvars.copy())

class GenExpression(Expression):
    def __init__(self, expr=None, quantifiers=None, domains=None, primed=False):
        self.expr = expr
        self.quantifiers = quantifiers
        self.domains = domains
        self.primed = primed

    def __str__(self):
        return "Gen(" + self.expr.__str__() \
                        + ", " + str(self.quantifiers) + ")"

    def substitute(self, subs):
        domains = [ expr.substitute(subs) for expr in self.domains ]
        expr = self.expr.substitute(subs)
        return GenExpression(expr=expr, quantifiers=self.quantifiers,
                                domains=domains, primed=self.primed)

    def enumerate(self, containers, domains, boundedvars, result):
        if domains == []:
            result.append(self.expr.eval(containers, boundedvars))
        else:
            (var, domain) = domains[0]
            domain = sorted(domain, key=lambda x: key(x))
            for val in domain:
                boundedvars[var] = ValueExpression(val)
                self.enumerate(containers, domains[1:], boundedvars, result)

    def eval(self, containers, boundedvars):
        domains = []
        for i in range(len(self.quantifiers)):
            domains += [ (self.quantifiers[i],
                            self.domains[i].eval(containers, boundedvars)) ]
        result = []
        self.enumerate(containers, domains, boundedvars.copy(), result)
        return frozenset(result)

class Temporal_existsExpression(Expression):
    def __init__(self, quantifiers=None, expr=None, containers=None, primed=False):
        self.quantifiers = quantifiers
        self.expr = expr
        self.containers = containers
        self.primed = self.expr.primed

    def __str__(self):
        return "TempExists(" + str(self.quantifiers) + ", " + self.expr.__str__() + ")"

    def substitute(self, subs):
        global initializing
        if initializing:
            containers = subs.copy()
            for id in self.quantifiers:
                containers[id] = ContainerExpression(var=id)
            return Temporal_existsExpression(quantifiers=self.quantifiers,
                    expr=self.expr.substitute(containers),
                    containers=containers, primed=self.primed)
        else:
            return Temporal_existsExpression(quantifiers=self.quantifiers,
                    expr=self.expr.substitute(subs),
                    containers=self.containers,
                    primed=self.primed)

    def eval(self, containers, boundedvars):
        return self.expr.eval(self.containers, boundedvars)

class RecorddefExpression(Expression):
    def __init__(self, kvs=None, primed=False):
        self.kvs = kvs
        self.primed = primed

    def fromAST(self, ast):
        (t, a) = ast
        assert t == "CommaList"
        self.kvs = dict()
        self.primed = False
        for (t2, a2) in a:
            assert t2 == "Concat"
            assert len(a2) == 3
            (t3, a3) = a2[0]
            assert t3 == "Name"
            expr = compileExpression(a2[2])
            self.kvs[lexeme(a3)] = expr
            self.primed = self.primed or expr.primed
        return self

    def __str__(self):
        result = ""
        for (k, e) in self.kvs.items():
            if result != "":
                result += ", "
            result += str(k) + ": " + e.__str__()
        return "Recorddef(" + result + ")"

    def substitute(self, subs):
        kvs = { k:v.substitute(subs) for (k, v) in self.kvs.items() }
        return RecorddefExpression(kvs=kvs, primed=self.primed)

    def expand(self, keys, record, result, containers, boundedvars):
        if keys == []:
            result.append(simplify(FrozenDict(record.copy())))
        else:
            k = keys[0]
            v = self.kvs[k]
            r = v.eval(containers, boundedvars)
            r = sorted(r, key=lambda x: key(x))
            for e in r:
                record[k] = e
                self.expand(keys[1:], record, result, containers, boundedvars)

    def eval(self, containers, boundedvars):
        keys = list(self.kvs.keys())
        keys = sorted(keys, key=lambda x: key(x))
        result = []
        self.expand(keys, {}, result, containers, boundedvars)
        return frozenset(result)

class RecordvalueExpression(Expression):
    def __init__(self, kvs=None, primed=False):
        self.kvs = kvs
        self.primed = primed

    def fromAST(self, ast):
        (t, a) = ast
        assert t == "CommaList"
        self.kvs = dict()
        self.primed = False
        for (t2, a2) in a:
            assert t2 == "Concat"
            assert len(a2) == 3
            (t3, a3) = a2[0]
            assert t3 == "Name"
            expr = compileExpression(a2[2])
            self.kvs[lexeme(a3)] = expr
            self.primed = self.primed or expr.primed
        return self

    def __str__(self):
        result = ""
        for (k, e) in self.kvs.items():
            if result != "":
                result += ", "
            result += str(k) + ": " + e.__str__()
        return "Recordvalue(" + result + ")"

    def substitute(self, subs):
        kvs = { k:v.substitute(subs) for (k, v) in self.kvs.items() }
        return RecordvalueExpression(kvs=kvs, primed=self.primed)

    def eval(self, containers, boundedvars):
        kvs = dict()
        keys = self.kvs.keys()
        for k in sorted(keys, key=lambda x: key(x)):
            kvs[k] = self.kvs[k].eval(containers, boundedvars)
        return simplify(FrozenDict(kvs))

class FuncsetExpression(Expression):
    def __init__(self, lhs=None, rhs=None, primed=False):
        self.lhs = lhs
        self.rhs = rhs
        self.primed = primed

    def fromAST(self, exprs):
        assert len(exprs) == 2
        self.lhs = compileExpression(exprs[0])
        self.rhs = compileExpression(exprs[1])
        self.primed = self.lhs.primed or self.rhs.primed
        return self

    def __str__(self):
        return "FuncSet(" + self.lhs.__str__() + ", " + self.rhs.__str__() + ")"

    def substitute(self, subs):
        return FuncsetExpression(
            lhs=self.lhs.substitute(subs),
            rhs=self.rhs.substitute(subs),
            primed=self.primed)

    def enumerate(self, lhs, rhs, record, result):
        if lhs == []:
            result.append(simplify(FrozenDict(record.copy())))
        else:
            for y in rhs:
                record[lhs[0]] = y
                self.enumerate(lhs[1:], rhs, record, result)

    def eval(self, containers, boundedvars):
        lhs = self.lhs.eval(containers, boundedvars)
        rhs = self.rhs.eval(containers, boundedvars)
        result = []
        self.enumerate(list(lhs), list(rhs), {}, result)
        return frozenset(result)

class ExceptExpression(Expression):
    def __init__(self, lhs=None, rhs=None, at=None, primed=False):
        self.lhs = lhs
        self.rhs = rhs
        self.at = at
        self.primed = primed

    def fromAST(self, exc):
        assert len(exc) == 2
        self.lhs = compileExpression(exc[0])
        self.at = BoundvarExpression("@")
        self.primed = self.lhs.primed
        (t, a) = exc[1]
        assert t == "GExcept"
        assert len(a) > 0
        self.rhs = []
        for (lst, expr) in a:
            args = []
            for arg in lst:
                (t2, a2) = arg
                assert t2 in {"elist", "efield"}
                (t3, a3) = a2
                if t2 == "elist":
                    assert t3 == "CommaList"
                    assert len(a3) > 0
                    indices = []
                    for e in a3:
                        ce = compileExpression(e)
                        if ce.primed:
                            self.primed = True
                        indices += [ce]
                    args += [indices]
                else:
                    assert t3 == "Name"
                    args += [[StringExpression(lexeme(a3))]]
            name_stack.append({ "@": self.at })
            cexpr = compileExpression(expr)
            name_stack.pop()
            if cexpr.primed:
                self.primed = True
            self.rhs += [(args, cexpr)]
        return self

    def __str__(self):
        result = ""
        for (args, expr) in self.rhs:
            ind = ""
            for a in args:
                if ind != "":
                    ind += ", "
                pos = ""
                for x in a:
                    if pos != "":
                        pos += ", "
                    pos += x.__str__()
                ind += "[" + pos + "]"
            if result != "":
                result += ", "
            result += "Replace(" + ind + ", " + expr.__str__() + ")"
        return "Except(" + self.lhs.__str__() + ", [" + result + "])"

    def substitute(self, subs):
        lhs = self.lhs.substitute(subs)
        rhs = []
        for (args, expr) in self.rhs:
            ind = []
            for a in args:
                pos = []
                for x in a:
                    pos += [ x.substitute(subs) ]
                ind += [ pos ]
            rhs += [(ind, expr.substitute(subs))]
        return ExceptExpression(lhs=lhs, rhs=rhs, at=self.at, primed=self.primed)

    def eval(self, containers, boundedvars):
        lhs = self.lhs.eval(containers, boundedvars)
        if isinstance(lhs, str) or isinstance(lhs, tuple):
            kvs = { (i+1):lhs[i] for i in range(len(lhs)) }
        else:
            assert isinstance(lhs, FrozenDict)
            kvs = lhs.d.copy()

        # Evaluate the exceptions
        for (iargs, iexpr) in self.rhs:
            assert len(iargs) == 1       # TODO doesn't handle ![][]...
            a = iargs[0]
            vals = [ arg.eval(containers, boundedvars) for arg in a ]
            newBVs = boundedvars.copy()
            old = funceval(lhs, vals)
            newBVs[self.at] = ValueExpression(old)
            new = iexpr.eval(containers, newBVs)
            if len(vals) == 1:
                kvs[vals[0]] = new
            else:
                kvs[tuple(vals)] = new
        return simplify(FrozenDict(kvs))

class PrimeExpression(Expression):
    def __init__(self, expr=None, primed=True):
        self.expr = expr
        assert primed
        self.primed = primed

    def fromAST(self, expr):
        self.expr = compileExpression(expr)
        assert self.expr.primed == False
        return self

    def __str__(self):
        return "Prime(" + self.expr.__str__() + ")"

    def substitute(self, subs):
        return PrimeExpression(expr=self.expr.substitute(subs))

    def eval(self, containers, boundedvars):
        assert isinstance(self.expr, ContainerExpression)
        assert self.expr.next != None
        return self.expr.next

class OutfixExpression(Expression):
    def __init__(self, op=None, expr=None, primed=False):
        self.op = op
        assert not isinstance(expr, tuple)
        self.expr = expr
        self.primed = primed

    def fromAST(self, prefix):
        (op, expr) = prefix
        lex = lexeme(op)
        self.op = "-." if lex == "-" else lex

        mod = modstk[-1]
        if self.op in mod.operators:
            id = mod.operators[self.op]
            assert isinstance(id, OperatorExpression)
            assert len(id.args) == 1
            args = [ compileExpression(expr) ]
            return opSubst([(op, id, args)])

        self.expr = compileExpression(expr)
        assert not isinstance(self.expr, tuple)

        if self.op == "-." and isinstance(self.expr, NumberExpression):
            return NumberExpression(-self.expr.number)
        self.primed = self.expr.primed
        return self

    def __str__(self):
        return "Outfix(\"" + self.op + "\", " + self.expr.__str__() + ")"

    def substitute(self, subs):
        # TODO.  Perhaps operator itself must be substituted?
        assert subs.get(self.op) == None

        global initializing
        if self.op == "[]" and initializing:
            initializing = False
            expr=self.expr.substitute(subs)
            initializing = True
            return OutfixExpression(op=self.op,
                    expr=expr, primed=self.primed)

        return OutfixExpression(op=self.op,
                    expr=self.expr.substitute(subs), primed=self.primed)

    def always(self, containers, boundedvars):
        assert isinstance(self.expr, SquareExpression)

        ok = True
        for (k, v) in containers.items():
            if v.next == None:
                print("always: UNASSIGNED", k)
                ok = False
        assert ok

        op = self.expr.lhs
        tries = 0
        i = 0
        while True:
            global maxcount

            if not silent:
                s = { k.id:c.next for (k, c) in containers.items() }
                print("Next state:", i, format(FrozenDict(s)))
            if maxcount != None and i >= maxcount:
                exit(0)
            for c in containers.values():
                c.prev = c.next
                c.next = None
            r = op.eval(containers, boundedvars)
            if r:
                changed = False
                for c in containers.values():
                    if c.next != c.prev:
                        changed = True
                        break
                if not changed:
                    if not silent:
                        print("State unchanged")
                    break
                tries = 0
            else:
                for c in containers.values():
                    c.next = c.prev
                tries += 1
                if verbose or tries % 100 == 0:
                    print("always: try again", tries)
                    time.sleep(1)
            i += 1

    def unchanged(self, expr):
        if isinstance(expr, TupleExpression):
            for x in expr.exprs:
                r = self.unchanged(x)
                if not r:
                    return False
        else:
            assert isinstance(expr, ContainerExpression)
            if expr.next != None and expr.next != expr.prev:
                return False
            expr.next = expr.prev
        return True

    def eval(self, containers, boundedvars):
        if self.op == "UNCHANGED":
            return self.unchanged(self.expr)

        if self.op == "[]":
            return self.always(containers, boundedvars)

        v = self.expr.eval(containers, boundedvars)

        print("Outfix operator", self.op, "not defined")
        assert False

class ChooseExpression(Expression):
    def __init__(self, id=None, domain=None, expr=None, primed=False):
        self.id = id
        self.domain = domain
        self.expr = expr
        self.primed = primed

    def fromAST(self, expr):
        assert len(expr) == 3
        (t, a) = expr[0]
        assert t == "Identifier"
        self.id = BoundvarExpression(lexeme(a))
        (t1, a1) = expr[1]
        assert t1 == "Optional"
        self.domain = None if a1 == None else compileExpression(a1)

        name_stack.append({ self.id.id:self.id })
        self.expr = compileExpression(expr[2])
        name_stack.pop()
        self.primed = False
        return self

    def __str__(self):
        return "Choose(" + str(self.id) + ", " + self.domain.__str__() \
                                + ", " + self.expr.__str__() + ")"

    def substitute(self, subs):
        return ChooseExpression(id=self.id,
            domain=None if self.domain == None else self.domain.substitute(subs),
            expr=self.expr.substitute(subs), primed=self.primed)

    def eval(self, containers, boundedvars):
        newBV = boundedvars.copy()
        if self.domain == None:
            if isinstance(self.expr, InfixExpression) \
                    and lexeme(self.expr.op) in { "=", "\\in", "\\notin" } \
                    and isinstance(self.expr.lhs, BoundvarExpression) \
                    and self.expr.lhs == self.id:
                if lexeme(self.expr.op) == "=":
                    func = self.expr.rhs
                    newBV[self.id] = func
                    return func.eval(containers, newBV)
                if lexeme(self.expr.op) == "\\in":
                    func = self.expr.rhs
                    newBV[self.id] = func
                    s = sorted(func.eval(containers, newBV), key=lambda x: key(x))
                    return s[0]
                if lexeme(self.expr.op) == "\\notin":
                    # CHOOSE of same expression should return same value...
                    x = format(self.expr.rhs)
                    return Nonce(x.__hash__())
                assert False
            elif isinstance(self.expr, ValueExpression) \
                    and isinstance(self.expr.value, bool):
                return Nonce(self.expr.value.__hash__())
        else:
            domain = sorted(self.domain.eval(containers, boundedvars),
                                        key=lambda x: key(x))
            for x in domain:
                newBV[self.id] = ValueExpression(x)
                r = self.expr.eval(containers, newBV)
                if r:
                    return x
        print("CHOOSE", self)
        assert False

    def apply(self, containers, boundedvars, fargs):
        newBV = boundedvars.copy()
        if self.domain == None \
                and isinstance(self.expr, InfixExpression) \
                and lexeme(self.expr.op) == "=" \
                and isinstance(self.expr.lhs, BoundvarExpression) \
                and self.expr.lhs == self.id:
            func = self.expr.rhs
            newBV[self.id] = func
            return func.apply(containers, newBV, fargs)
        else:
            v = self.eval(containers, boundedvars)
            return funceval(v, fargs)

# TODO.  Can potentiallly get rid of this in favor of CaseExpression
class IfExpression(Expression):
    def __init__(self, cond=None, ifexpr=None, elseexpr=None, primed=False):
        self.cond = cond
        self.ifexpr = ifexpr
        self.elseexpr = elseexpr
        self.primed = primed

    def fromAST(self, expr):
        assert len(expr) == 3
        self.cond = compileExpression(expr[0])
        self.ifexpr = compileExpression(expr[1])
        self.elseexpr = compileExpression(expr[2])
        self.primed = self.cond.primed or self.ifexpr.primed \
                                        or self.elseexpr.primed
        return self

    def __str__(self):
        return "If(" + self.cond.__str__() + ", " + self.ifexpr.__str__() \
                                + ", " + self.elseexpr.__str__() + ")"

    def substitute(self, subs):
        return IfExpression(
            cond=self.cond.substitute(subs),
            ifexpr=self.ifexpr.substitute(subs),
            elseexpr=self.elseexpr.substitute(subs),
            primed=self.primed
        )

    def eval(self, containers, boundedvars):
        cond = self.cond.eval(containers, boundedvars)
        if cond:
            return self.ifexpr.eval(containers, boundedvars)
        else:
            return self.elseexpr.eval(containers, boundedvars)

class CaseExpression(Expression):
    def __init__(self, cases=None, other=None, primed=False):
        self.cases = cases
        self.other = other
        self.primed = primed

    def fromAST(self, expr):
        (t0, a0) = expr[0]
        assert t0 == "SeparatorList"
        (t1, a1) = expr[1]
        assert t1 == "Optional"

        self.primed = False
        self.cases = []
        for (t2, a2) in a0:
            assert t2 == "Concat"
            cond = compileExpression(a2[0])
            val = compileExpression(a2[2])
            self.cases += [ (cond, val) ]
            if cond.primed or val.primed:
                self.primed = True

        if a1 == None:
            self.other = None
        else:
            self.other = compileExpression(a1)
            self.primed = self.primed or self.other.primed

        return self

    def __str__(self):
        result = ""
        for (c, e) in self.cases:
            if result != "":
                result += " [] "
            result += c.__str__() + " -> " + e.__str__()
        if self.other != None:
            result += " [] OTHER -> " + self.other.__str__()
        return "Case(" + result + ")"

    def substitute(self, subs):
        cases = [ (cond.substitute(subs), expr.substitute(subs))
                                        for (cond, expr) in self.cases ]
        other = None if self.other == None else self.other.substitute(subs)
        return CaseExpression(cases=cases, other=other, primed=self.primed)

    def eval(self, containers, boundedvars):
        cases = random.sample(self.cases, len(self.cases))
        for (c, e) in cases:
            r = c.eval(containers, boundedvars)
            if r:
                return e.eval(containers, boundedvars)
        assert self.other != None
        return self.other.eval(containers, boundedvars)

class LetExpression(Expression):
    def __init__(self, mod=None, expr=None, primed=False):
        self.mod = mod
        self.expr = expr
        self.primed = primed

    def fromAST(self, expr):
        assert len(expr) == 2
        (t, a) = expr[0]
        assert t == "AtLeast1"

        # LET is treated like a mini-module
        self.mod = Module()
        mod = modstk[-1]
        self.mod.variables = mod.variables.copy()
        self.mod.constants = mod.constants.copy()
        self.mod.operators = mod.operators.copy()
        self.mod.wrappers = mod.wrappers.copy()
        self.mod.globals = mod.globals.copy()
        modstk.append(self.mod)
        ops = {}
        name_stack.append(ops)
        for d in a:
            (t1, a1) = d
            if t1 == "GOperatorDefinition":
                (id, args, e) = compileOperatorDefinition(a1)
            else:
                assert t1 == "GFunctionDefinition"  # deal with ModDef later
                (id, args, e) = compileFunctionDefinition(a1)
            od = OperatorExpression(id, args, e)
            self.mod.operators[id] = od
            self.mod.globals.add(id)
            ops[id] = od
        self.expr = compileExpression(expr[1])
        name_stack.pop()
        modstk.pop()

        return self.expr        # make "LET" disappear

    def __str__(self):
        if False:
            return "Let(" + str(self.mod.operators) + ", " + self.expr.__str__() + ")"
        else:
            return "Let(" + self.expr.__str__() + ")"

    def substitute(self, subs):
        # return LetExpression(mod=self.mod,
        #     expr=self.expr.substitute(subs),
        #     primed=self.primed)
        assert False

    def eval(self, containers, boundedvars):
        assert False

# Cartesian product
class CartesianExpression(Expression):
    def __init__(self, exprs=None, primed=False):
        self.exprs = exprs
        self.primed = primed

    def fromAST(self, cart):
        self.exprs = [ compileExpression(x) for x in cart ]
        self.primed = any(x.primed for x in self.exprs)
        return self

    def __str__(self):
        result = ""
        for x in self.exprs:
            if result != "":
                result += ", "
            result += x.__str__()
        return "Cartesian(" + result + ")"

    def substitute(self, subs):
        exprs = [ x.substitute(subs) for x in self.exprs ]
        return CartesianExpression(exprs=exprs, primed=self.primed)

    def enumerate(self, exprs, tup, result):
        if exprs == []:
            result.append(tuple(tup))
        else:
            for x in exprs[0]:
                self.enumerate(exprs[1:], tup + [x], result)

    def eval(self, containers, boundedvars):
        exprs = [ x.eval(containers, boundedvars) for x in self.exprs ]
        result = []
        self.enumerate(exprs, [], result)
        return frozenset(result)

class InfixExpression(Expression):
    def __init__(self, op=None, lhs=None, rhs=None, primed=False):
        self.op = op
        self.lhs = lhs
        self.rhs = rhs
        self.primed = primed

    def fromAST(self, infix):
        (op, lhs, rhs) = infix

        lex = lexeme(op)
        lt = compileExpression(lhs)
        rt = compileExpression(rhs)
        mod = modstk[-1]
        
        if lex in mod.operators:
            id = mod.operators[lex]
            assert isinstance(id, OperatorExpression)
            assert len(id.args) == 2
            return opSubst([(op, id, [ lt, rt ])])

        self.op = op
        self.lhs = lt
        self.rhs = rt
        self.primed = self.lhs.primed or self.rhs.primed
        return self

    def __str__(self):
        return "Infix(\"" + str(self.op) + "\", " + self.lhs.__str__() \
                                    + ", " + self.rhs.__str__() + ")"

    def substitute(self, subs):
        return InfixExpression(op=self.op,
            lhs=self.lhs.substitute(subs), rhs=self.rhs.substitute(subs),
            primed=self.primed)

    def eval(self, containers, boundedvars):
        global IO_outputs           # IO_outputs behaves as a hidden variable

        lex = lexeme(self.op)

        # One special case is if the expression is of the form x' = ...
        # when x' is not assigned a value in next.  In that case we set
        # x' to ...
        if isinstance(self.lhs, PrimeExpression):
            var = self.lhs.expr
            assert isinstance(var, ContainerExpression)
            if var.next == None:
                val = self.rhs.eval(containers, boundedvars)
                if val == None:
                    print("XXX", self.rhs)
                assert val != None
                if lex == '=':
                    var.next = val
                    # print("ASSIGN", var.var, containers)
                    return True
                elif lex == "\\in":
                    lst = list(val)
                    r = random.randrange(len(lst))
                    var.next = lst[r]
                    return True

        # Copy next state in case need to restore after OR operation
        # with FALSE left hand side.  Also, randomize lhs/rhs
        # evaluation
        if lex == "\\/":
            output_copy = IO_outputs.copy()
            copy = {}
            for (k, v) in containers.items():
                copy[k] = v.next
            r = random.randrange(2)
            if r == 0:
                lhs = self.lhs.eval(containers, boundedvars)
            else:
                assert r == 1
                rhs = self.rhs.eval(containers, boundedvars)
        else:
            r = 0
            lhs = self.lhs.eval(containers, boundedvars)

        if lex == "\\/":
            if (r == 0) and lhs:
                return lhs
            if (r == 1) and rhs:
                return rhs
            # restore and evaluate right hand side
            for (k, v) in copy.items():
                containers[k].next = v
            IO_outputs = output_copy
        elif lex == "/\\":
            assert r == 0
            if not lhs:
                return False
        if r == 0:
            rhs = self.rhs.eval(containers, boundedvars)
        else:
            lhs = self.lhs.eval(containers, boundedvars)

        # print("INFIX EVAL", lex, lhs, rhs)

        try:
            if lex == "/\\": return lhs and rhs
            if lex == "\\/": return lhs or rhs
            if lex == "=": return lhs == rhs
            if lex == "\\in": return lhs in rhs
            if lex == "\\notin": return lhs not in rhs
        except Exception as e:
            print("Evaluating infix", stringToken(self.op), "failed")
            print(e)
            print(traceback.format_exc())
            exit(1)

        print("Infix operator", self.op, "not defined")
        assert False

# Apply the given arguments in vals to func
def funceval(func, vals):
    assert func != None

    # strings are special case of functions
    if isinstance(func, str):
        assert len(vals) == 1
        assert vals[0] >= 1
        assert vals[0] <= len(func)
        return func[vals[0] - 1]

    # Turn function into a dictionary
    if isinstance(func, tuple):
        assert len(vals) == 1
        assert vals[0] >= 1
        assert vals[0] <= len(func)
        kvs = { (i+1):func[i] for i in range(len(func)) }
    else:
        assert isinstance(func, FrozenDict)
        kvs = func.d

    # See if there's a match against the kvs
    if len(vals) == 1:
        k = vals[0]
    else:
        k = tuple(vals)
    v = kvs.get(k)
    if v != None:
        return v

    print("FUNCEVAL", func, vals, kvs, k)
    assert False

# v is either a string, a tuple of values, or a FrozenDict.
# Return a uniform representation such that if two values should
# be equal they have the same representation.  Strings are the preferred
# representation, then tuples, then sets, then records, then nonces.
def simplify(v):
    if len(v) == 0:
        return ""
    if isinstance(v, str):
        return v

    # See if it's a record that can be converted into a tuple
    if isinstance(v, FrozenDict):
        kvs = v.d
        if set(kvs.keys()) == set(range(1, len(v) + 1)):
            t = []
            for i in range(1, len(v) + 1):
                t += [kvs[i]]
            v = tuple(t)

    # See if it's a tuple that can be converted into a string:
    if isinstance(v, tuple) and \
            all(isinstance(c, str) and len(c) == 1 for c in v):
        return "".join(v)

    return v

class IndexExpression(Expression):
    def __init__(self, token=None, func=None, args=None, primed=None):
        self.token = token
        self.func = func
        self.args = args
        self.primed = primed

    def fromAST(self, expr):
        (token, func, args) = expr
        self.token = token
        self.func = compileExpression(func)
        self.primed = self.func.primed
        (t, a) = args
        assert t == "CommaList"
        self.args = []
        for ast in a:
            ca = compileExpression(ast)
            if ca.primed:
                self.primed = True
            self.args += [ca]
        assert self.args != []
        return self

    def __str__(self):
        assert self.args != []
        result = ""
        for x in self.args:
            if result != "":
                result += ", "
            result += x.__str__()
        return "Index(" + self.func.__str__() + ", [" + result + "])"

    def substitute(self, subs):
        assert self.args != []
        func = self.func.substitute(subs)
        args = [ arg.substitute(subs) for arg in self.args ]
        assert args != []
        return IndexExpression(func=func, args=args, primed=self.primed)

    def eval(self, containers, boundedvars):
        assert self.args != []
        args = [ arg.eval(containers, boundedvars) for arg in self.args ]
        r = self.func.apply(containers, boundedvars, args)
        assert r != None
        return r

class TupleExpression(Expression):
    def __init__(self, exprs=None, primed=False):
        self.exprs = exprs
        self.primed = primed

    def fromAST(self, ast):
        self.primed = False
        (t, a) = ast
        assert t == "Optional"
        if a == None:
            self.exprs = []
        else:
            (t1, a1) = a
            assert t1 == "CommaList"
            self.exprs = [compileExpression(x) for x in a1]
            for e in self.exprs:
                if e.primed:
                    self.primed = True
                    break
        return self

    def __str__(self):
        result = ""
        for x in self.exprs:
            if result != "":
                result += ", "
            if x == None:
                result += "None"
            else:
                result += x.__str__()
        return "Tuple(" + result + ")"

    def substitute(self, subs):
        return TupleExpression(
            exprs=[ e.substitute(subs) for e in self.exprs ],
            primed=self.primed
        )

    def eval(self, containers, boundedvars):
        return simplify(tuple([ e.eval(containers, boundedvars) for e in self.exprs ]))

    def apply(self, containers, boundedvars, fargs):
        assert len(fargs) == 1
        # print("ZZZZ", [x.eval(containers, boundedvars) for x in self.exprs], fargs[0])
        return self.exprs[fargs[0] - 1].eval(containers, boundedvars)

class SetExpression(Expression):
    def __init__(self, elements=None, primed=False):
        self.elements = elements
        self.primed = primed

    def fromAST(self, ast):
        (t, a) = ast
        assert t == "Optional"
        self.primed = False
        self.elements = []
        if a != None:
            (t0, a0) = a
            assert t0 == "CommaList"
            for x in a0:
                cx = compileExpression(x)
                if cx.primed:
                    self.primed = True
                self.elements += [ cx ]
        return self

    def __str__(self):
        result = ""
        for x in self.elements:
            if result != "":
                result += ", "
            if x == None:
                result += "None"
            else:
                result += x.__str__()
        return "Set(" + result + ")"

    def substitute(self, subs):
        return SetExpression(
            elements=[ e.substitute(subs) for e in self.elements ],
            primed=self.primed
        )

    def eval(self, containers, boundedvars):
        result = set()
        for x in self.elements:
            result.add(x.eval(containers, boundedvars))
        return frozenset(result)

class FilterExpression(Expression):
    def __init__(self, vars=None, elements=None, expr=None, primed=False):
        self.vars = vars
        self.elements = elements
        self.expr = expr
        self.primed = primed

    def fromAST(self, filter):
        (t0, a0) = filter[0]
        if t0 == "Identifier":
            self.vars = [BoundvarExpression(lexeme(a0))]
        else:
            assert t0 == "Tuple"
            (t1, a1) = a0
            assert t1 == "CommaList"
            self.vars = [ BoundvarExpression(v) for (t, v) in a1 ]
        self.elements = compileExpression(filter[1])
        name_stack.append({ bv.id:bv for bv in self.vars })
        self.expr = compileExpression(filter[2])
        name_stack.pop()
        return self

    def __str__(self):
        return "Filter(" + str(self.vars) + ", " + self.elements.__str__() \
                        + ", " + self.expr.__str__() + ")"

    def substitute(self, subs):
        return FilterExpression(
            vars=self.vars,
            elements=self.elements.substitute(subs),
            expr=self.expr.substitute(subs),
            primed=self.primed
        )

    def eval(self, containers, boundedvars):
        result = set()
        assert len(self.vars) == 1
        elements = self.elements.eval(containers, boundedvars)
        result = []
        bvs = boundedvars.copy()
        assert len(self.vars) == 1      # TODO

        # Need to go through elements in defined order because
        # of pseudo-randomization
        elements = sorted(elements, key=lambda x: key(x))

        for x in elements:
            bvs[self.vars[0]] = ValueExpression(x)
            if self.expr.eval(containers, bvs):
                result.append(x)
        return frozenset(result)

class NumberExpression(Expression):
    def __init__(self, n):
        self.number = int(n)
        self.primed = False

    def __str__(self):
        return "Number(" + str(self.number) + ")"

    def substitute(self, subs):
        return self

    def eval(self, containers, boundedvars):
        return self.number

class StringExpression(Expression):
    def __init__(self, s):
        self.string = s
        self.primed = False

    def __str__(self):
        return "String(\"" + self.string + "\")"

    def substitute(self, subs):
        return self

    def eval(self, containers, boundedvars):
        return self.string

    def apply(self, containers, boundedvars, fargs):
        assert len(fargs) == 1
        return self.string[fargs[0] - 1]

#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 
####    Main Class
#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 

name_stack[-1]["FALSE"] = ValueExpression(False)
name_stack[-1]["TRUE"] = ValueExpression(True)

class PlusPyError(Exception):
    def __init__(self, descr):
        self.descr = descr

    def __str__(self):
        return "PlusPyError: " + self.descr

class PlusPy:
    def __init__(self, file, constants={}, seed=None):
        if seed != None:
            random.seed(seed)

        # Load the module
        self.mod = Module()
        if not file.endswith(".tla"):
            file += ".tla"
        if not self.mod.load_from_file(file):
            raise PlusPyError("can't load " + file)
        modules[self.mod.name] = self.mod

        self.constants = {
            self.mod.constants[k]:ValueExpression(v) for (k, v) in constants.items()
        }
 
        # Substitute containers for variables
        self.containers = { v:ContainerExpression(var=v)
                                    for v in self.mod.variables.values() }

    def init(self, initOp):
        op = self.mod.operators[initOp]
        assert isinstance(op, OperatorExpression)
        assert op.args == []

        # Set the constants
        expr2 = op.expr.substitute(self.constants)

        # Replace variables with primed containers in state expressions
        global initializing
        initializing = True
        expr3 = expr2.substitute(self.containers)
        initializing = False
        r = expr3.eval(self.containers, {})
        if not r:
            print("Initialization failed -- fatal error", file=sys.stderr)
            exit(1)

        ok = True
        for (k, v) in self.containers.items():
            if v.next == None:
                print("UNASSIGNED", k)
                ok = False
        assert ok

    # This is really solving the satisfiability problem
    # However, we make only one randomized attempt
    def trynext(self, expr, args, arg):
        # set previous state to next state and next state to None
        for c in self.containers.values():
            c.prev = c.next
            c.next = None

        # Replace operator arguments with specified values
        # TODO.  Should be able to take more than 1 argument
        if len(args) > 0:
            expr = expr.substitute({ args[0] : ValueExpression(arg) })

        # Replace constants for their values and variables for containers
        expr2 = expr.substitute(self.constants)
        expr3 = expr2.substitute(self.containers)

        # Evaluate
        r = expr3.eval(self.containers, {})
        if r:
            error = False
            for (v, c) in self.containers.items():
                if c.next == None:
                    print("Variable", v.id, "did not receive a value (fatal error)", file=sys.stderr)
                    error = True
            if error:
                exit(1)
        else:
            for c in self.containers.values():
                c.next = c.prev
        return r

    # TODO.  Should support multiple arguments
    def next(self, nextOp, arg=None):
        op = self.mod.operators[nextOp]
        assert isinstance(op, OperatorExpression)
        return self.trynext(op.expr, op.args, arg)

    # Check of state has not changed
    def unchanged(self):
        for c in self.containers.values():
            if c.next != c.prev:
                return False
        return True

    def get(self, var):
        var = self.mod.variables.get(var)
        if var == None:
            return None
        return self.containers[var].next

    def set(self, var, value):
        v = self.containers.get(self.mod.variables[var])
        v.next = value

    def getall(self):
        s = { k.id:v.next for (k, v) in self.containers.items() }
        return simplify(FrozenDict(s))

#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 
####    Python Wrappers (to replace TLA+ operator definitions)
#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 

class Wrapper:
    def eval(self, id, args):
        assert False

class InfixWrapper(Wrapper):
    def __str__(self):
        return "Naturals!InfixWrapper()"

    def eval(self, id, args):
        assert len(args) == 2
        lhs = args[0]
        rhs = args[1]
        if id[0] == "\\":
            if id == "\\/": return lhs or rhs
            if id == "\\equiv": return lhs == rhs
            if id == "\\geq": return lhs >= rhs
            if id == "\\in": return lhs in rhs
            if id == "\\notin": return lhs not in rhs
            if id == "\\leq": return lhs <= rhs
            if id == "\\subset": return lhs.issubset(rhs) and lhs != rhs
            if id == "\\subseteq": return lhs.issubset(rhs)
            if id == "\\supset": return rhs.issubset(lhs) and rhs != lhs
            if id == "\\supseteq": return rhs.issubset(lhs)
            if id == "\\": return lhs.difference(rhs)
            if id in { "\\cap", "\\intersect" }: return lhs.intersection(rhs)
            if id in { "\\cup", "\\union" }: return lhs.union(rhs)
            if id == "\\div": return lhs // rhs
        else:
            if id == "/\\": return lhs and rhs
            if id == "=>": return (not lhs) or rhs
            if id == "<=>": return lhs == rhs
            if id in { "#", "/=" }: return lhs != rhs
            if id == "<": return lhs < rhs
            if id == "=": return lhs == rhs
            if id == ">": return lhs > rhs
            if id == ">=": return lhs >= rhs
            if id in { "<=", "=<" }: return lhs <= rhs
            if id == "..": return frozenset({ i for i in range(lhs, rhs + 1) })
            if id == "+": return lhs + rhs
            if id == "-": return lhs - rhs
            if id == "*": return lhs * rhs
            if id == "/": return lhs / rhs
            if id == "%": return lhs % rhs
            if id == "^": return lhs ** rhs
        assert False

class OutfixWrapper(Wrapper):
    def __str__(self):
        return "Naturals!OutfixWrapper()"

    def subset_enum(self, lst, record, result):
        if lst == []:
            result.add(frozenset(record))
        else:
            self.subset_enum(lst[1:], record, result)
            self.subset_enum(lst[1:], record.union({ lst[0] }), result)

    def eval(self, id, args):
        assert len(args) == 1
        expr = args[0]

        if id == "DOMAIN":
            if isinstance(expr, str) or isinstance(expr, tuple):
                return frozenset(range(1, len(expr) + 1))
            else:
                assert isinstance(expr, FrozenDict)
                return frozenset(expr.d.keys())

        if id == "UNION":
            result = set()
            for x in expr:
                result = result.union(x)
            return frozenset(result)

        if id == "SUBSET":
            result = set()
            self.subset_enum(list(expr), set(), result)
            return frozenset(result)

        # if id == "-.": return -expr
        if id in { "~", "\\lnot", "\\neg" }: return not expr

        assert False

wrappers["Core"] = {
    "=>": InfixWrapper(),
    "<=>": InfixWrapper(),
    "\\equiv": InfixWrapper(),
    # "/\\": InfixWrapper(),
    # "\\/": InfixWrapper(),
    "#": InfixWrapper(),
    "/=": InfixWrapper(),
    # "=": InfixWrapper(),
    # "\\in": InfixWrapper(),
    # "\\notin": InfixWrapper(),
    "\\subset": InfixWrapper(),
    "\\subseteq": InfixWrapper(),
    "\\supset": InfixWrapper(),
    "\\supseteq": InfixWrapper(),
    "\\": InfixWrapper(),
    "\\cap": InfixWrapper(),
    "\\intersect": InfixWrapper(),
    "\\cup": InfixWrapper(),
    "\\union": InfixWrapper(),
    "DOMAIN": OutfixWrapper(),
    "~": OutfixWrapper(),
    "\\lnot": OutfixWrapper(),
    "\\neg": OutfixWrapper(),
    "UNION": OutfixWrapper(),
    "SUBSET": OutfixWrapper()
}

wrappers["Naturals"] = {
    "<": InfixWrapper(),
    ">": InfixWrapper(),
    ">=": InfixWrapper(),
    "\\geq": InfixWrapper(),
    "<=": InfixWrapper(),
    "=<": InfixWrapper(),
    "\\leq": InfixWrapper(),
    "..": InfixWrapper(),
    "+": InfixWrapper(),
    "-": InfixWrapper(),
    "*": InfixWrapper(),
    "/": InfixWrapper(),
    "\\div": InfixWrapper(),
    "%": InfixWrapper(),
    "^": InfixWrapper(),
}

class LenWrapper(Wrapper):
    def __str__(self):
        return "Sequences!Len(_)"

    def eval(self, id, args):
        assert len(args) == 1
        assert isinstance(args[0], tuple) or isinstance(args[0], str)
        return len(args[0])

class ConcatWrapper(Wrapper):
    def __str__(self):
        return "Sequences!Concat(_)"

    def eval(self, id, args):
        assert len(args) == 2
        return simplify(tuple(list(args[0]) + list(args[1])))

class AppendWrapper(Wrapper):
    def __str__(self):
        return "Sequences!Append(_)"

    def eval(self, id, args):
        assert len(args) == 2
        return simplify(tuple(list(args[0]) + [args[1]]))

wrappers["Sequences"] = {
    "Len": LenWrapper(),
    "\\o": ConcatWrapper(),
    "Append": AppendWrapper()
}

class AssertWrapper(Wrapper):
    def __str__(self):
        return "TLC!Assert(_, _)"

    def eval(self, id, args):
        assert len(args) == 2
        assert args[0], args[1]
        return True

class JavaTimeWrapper(Wrapper):
    def __str__(self):
        return "TLC!JavaTime()"

    def eval(self, id, args):
        assert len(args) == 0
        return int(time.time() * 1000)

class PrintWrapper(Wrapper):
    def __str__(self):
        return "TLC!Print(_)"

    def eval(self, id, args):
        assert len(args) == 2
        print(str(convert(args[0])), end="")
        return args[1]

class RandomElementWrapper(Wrapper):
    def __str__(self):
        return "TLC!RandomElement(_)"

    def eval(self, id, args):
        assert len(args) == 1
        lst = list(args[0])
        r = random.randrange(len(lst))
        return lst[r]

class ToStringWrapper(Wrapper):
    def __str__(self):
        return "TLC!ToString(_)"

    def eval(self, id, args):
        assert len(args) == 1
        return str(format(args[0]))

TLCvars = {}

class TLCSetWrapper(Wrapper):
    def __str__(self):
        return "TLC!TLCSet(_, _)"

    def eval(self, id, args):
        assert len(args) == 2
        TLCvars[args[0]] = args[1]
        return True

class TLCGetWrapper(Wrapper):
    def __str__(self):
        return "TLC!TLCGet(_)"

    def eval(self, id, args):
        assert len(args) == 1
        return TLCvars[args[0]]

wrappers["TLC"] = {
    "Assert": AssertWrapper(),
    "JavaTime": JavaTimeWrapper(),
    # "Print": PrintWrapper(),
    "RandomElement": RandomElementWrapper(),
    "TLCSet": TLCSetWrapper(),
    "TLCGet": TLCGetWrapper(),
    "ToString": ToStringWrapper()
}

import threading

class netReceiver(threading.Thread):
    def __init__(self, src, mux):
        threading.Thread.__init__(self)
        self.src = src
        self.mux = mux

    def run(self):
        global IO_inputs

        (skt, addr) = self.src
        (host, port) = addr
        all=[]
        while True:
            data = skt.recv(8192)
            if not data:
                break
            all.append(data)
        with lock:
            msg = pickle.loads(b''.join(all))
            if verbose:
                print("netReceiver", addr, msg)
            IO_inputs.append(FrozenDict({
                "intf": "tcp", "mux": self.mux, "data": msg}
            ))
            cond.notify()

class netSender(threading.Thread):
    def __init__(self, mux, msg):
        threading.Thread.__init__(self)
        self.mux = mux
        self.msg = msg

    def run(self):
        parts = self.mux.split(":")
        dst = (parts[0], int(parts[1]))
        if verbose:
            print("netSender", dst, self.msg)
        while True:
            try:
                skt = socket.socket(socket.AF_INET,socket.SOCK_STREAM)
                skt.connect(dst)
                skt.sendall(pickle.dumps(self.msg))
                skt.close()
                break
            except ConnectionRefusedError:
                time.sleep(0.5)

class netServer(threading.Thread):
    def __init__(self, mux):
        threading.Thread.__init__(self)
        self.mux = mux

    def run(self):
        skt = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
        skt.setsockopt(socket.SOL_SOCKET, socket.SO_REUSEADDR, 1)
        parts = self.mux.split(":")
        skt.bind((parts[0], int(parts[1])))
        skt.listen()
        while True:
            client = skt.accept()
            netReceiver(client, self.mux).start()

IO_inputs = []
IO_outputs = []
IO_running = set()

def flush():
    global IO_outputs
    for x in IO_outputs: 
        d = x.d
        if d["intf"] == "fd":
            if d["mux"] == "stdout":
                print(d["data"], end="")
                sys.stdout.flush()
            else:
                assert d["mux"] == "stderr"
                print(d["data"], end="", file=sys.stderr)
                sys.stderr.flush()
        elif d["intf"] == "tcp":
            netSender(d["mux"], d["data"]).start()
        else:
            assert False

def drain():
    global IO_outputs
    IO_outputs = []

class IOPutWrapper(Wrapper):
    def __str__(self):
        return "IO!IOPut(_)"

    def eval(self, id, args):
        assert len(args) == 3
        IO_outputs.append(FrozenDict(
            { "intf": args[0], "mux": args[1], "data": args[2] }
        ))
        return True

class Reader(threading.Thread):
    def run(self):
        global IO_inputs

        while True:
            inp = input()
            with lock:
                IO_inputs.append(FrozenDict(
                    { "intf": "fd", "mux": "stdin", "data": inp}
                ))
                cond.notify()

class IOWaitWrapper(Wrapper):
    def __str__(self):
        return "IO!IOWait(Pattern(_))"

    def eval(self, id, args):
        global IO_running

        assert len(args) == 2

        # First check if there's already input
        for x in IO_inputs:
            assert isinstance(x, FrozenDict)
            d = x.d
            if d["intf"] == args[0] and d["mux"] == args[1]:
                return True

        # If not, make sure a reader/receiver is running
        if (args[0], args[1]) not in IO_running:
            if args[0] == "fd" and args[1] == "stdin":
                Reader().start()
            elif args[0] == "tcp":
                netServer(args[1]).start()
            else:
                assert False
            IO_running.add((args[0], args[1]))

        return False

class IOGetWrapper(Wrapper):
    def __str__(self):
        return "IO!IOGet(Pattern(_))"

    def eval(self, id, args):
        assert len(args) == 2
        for x in IO_inputs:
            assert isinstance(x, FrozenDict)
            d = x.d
            if d["intf"] == args[0] and d["mux"] == args[1]:
                IO_inputs.remove(x)
                return d["data"]
        assert False

wrappers["IO"] = {
    "IOPut": IOPutWrapper(),
    "IOWait": IOWaitWrapper(),
    "IOGet": IOGetWrapper()
}

#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 
####    Main program
#### #### #### #### #### #### #### #### #### #### #### #### #### #### #### #### 

import sys
import time
import socket
import pickle
import getopt

lock = threading.Lock()
cond = threading.Condition(lock)
maxcount = None

def usage():
    print("Usage: pluspy [options] tla-module")
    print("  options: ")
    print("    -c cnt: max #times that Next should be evaluated")
    print("    -h: help")
    print("    -i operator: Init operator (default Init)")
    print("    -n operator: Next operator (default Next)")
    print("    -P path: module directory search path")
    print("    -s: silent")
    print("    -S seed: random seed")
    print("    -v: verbose output")
    exit(1)

def handleOutput(output):
    d = convert(output)
    if d["intf"] == "fd":
        if d["mux"] == "stdout":
            print(d["data"], end="")
        else:
            assert d["mux"] == "stderr"
            print(d["data"], end="", file=sys.stderr)
    else:
        print("GOT OUTPUT", d)
        assert False

step = 0

# The Next operator, possibly with arguments separated by "%"
def run(pp, next):
    global maxcount, verbose, silent, step

    args = next.split("%")
    assert 1 <= len(args) and len(args) <= 2
    if len(args) == 1:
        arg = ""
    elif all(isnumeral(c) for c in args[1]):
        arg = int(args[1])
    else:
        arg = args[1]
    while True:
        with lock:
            tries = 0
            flush()     # do all the outputs
            drain()     # remove all outputs
            while not pp.next(args[0], arg):
                tries += 1
                if verbose:
                    print("TRY AGAIN", tries, flush=True)
                if tries > 100:
                    cond.wait(0.2)
                drain()
                if maxcount != None and step >= maxcount:
                    break

            if maxcount != None and step >= maxcount:
                break
            if pp.unchanged():
                if not silent:
                    print("No state change after successful step", flush=True)
                break
            tries = 0
            if not silent:
                print("Next state:", step, format(pp.getall()), flush=True)
            step += 1

def main():
    global verbose, silent, maxcount, pluspypath

    if os.environ.get("PLUSPYPATH") != None:
        pluspypath = os.environ["PLUSPYPATH"]

    # Get options.  First set default values
    initOp = "Init"
    nextOps = set()
    seed = None
    try:
        opts, args = getopt.getopt(sys.argv[1:],
                        "c:hi:n:P:sS:v",
                        ["help", "init=", "next=", "path=", "seed="])
    except getopt.GetoptError as err:
        print(str(err))
        usage()
    for o, a in opts:
        if o in { "-v" }:
            verbose = True
        elif o in { "-c" }:
            maxcount = int(a)
        elif o in { "-h", "--help" }:
            usage()
        elif o in { "-i", "--init" }:
            initOp = a
        elif o in { "-n", "--next"  }:
            nextOps.add(a)
        elif o in { "-P", "--path" }:
            pluspypath = a
        elif o in { "-s" }:
            silent = True
        elif o in { "-S", "--seed" }:
            seed = int(a)
        else:
            assert False, "unhandled option"
    if len(args) != 1:
        usage()

    pp = PlusPy(args[0], seed=seed)
    mod = pp.mod
    if verbose:
        print("Loaded module", mod.name)

    if verbose:
        print()
        print("---------------")
        print("Initialize state")
        print("---------------")
    pp.init(initOp)
    if not silent:
        print("Initial context:", format(pp.getall()))

    if verbose:
        print()
        print("---------------")
        print("Run behavior for", maxcount, "steps")
        print("---------------")

    if len(nextOps) != 0:
        threads = set()
        for next in nextOps:
            t = threading.Thread(target=run, args=(pp, next))
            threads.add(t)
            t.start()
        for t in threads:
            t.join()
    else:
        run(pp, "Next")
    if not silent:
        print("MAIN DONE")
    exit(0)

if __name__ == "__main__":
    main()

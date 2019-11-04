#!/usr/bin/python3

from functools import reduce
from llvmlite import ir, binding
import sys
import json

#jsonir = json.loads(open(sys.argv[1], "r").read())

vars = {}
vertices = {}
functions = {}
import_functions = {}

module = ir.Module(name="test")

importfunctype = ir.FunctionType (ir.IntType (64), [])
voidfunctype = ir.FunctionType (ir.VoidType (), [])
abort = ir.Function (module, voidfunctype, "abort")

# Hack
M = ir.GlobalVariable (module, ir.PointerType (ir.IntType (8)), "M")

def get_builder_op(op, irb):
    exp_map = {
        'add': 'add',
        'and': 'and_',
        'invert': 'neg',
        'xor': 'xor',
        'asr': 'ashr',
        'umul': 'mul'
    }
    return getattr(irb, exp_map[op])

shifts = ['asr']
reduction = ['xor', 'add']

def convert_file (file, module):
    # Declare stuff

    # It is safe to not pass an irb because rax will always be a
    # global variable which won't use the builder
    rax = convert_var_noload (file['special_regs'] ['rax'])

    for func in file['functions'].items ():
        add_func (func, module)

    for func in file['functions'].items ():
        convert_func (func, module, rax)

    entry = ir.Function (module, voidfunctype, "main")
    init = ir.Function (module, voidfunctype, "initialize_stuff")
    block = entry.append_basic_block("entry")
    irb = ir.IRBuilder (block)
    irb.call (init, [])
    irb.call (functions [int (file['sourcefunc'])], [])
    irb.ret_void ()

def get_import_func (file, func):
    tuple = (file, func)
    if tuple not in import_functions:
        func = ir.Function (module, importfunctype, name="%s!%s" % (file, func))
        import_functions [tuple] = func

    return import_functions [tuple]

def add_func (func, module):
    addr = int (func[0])
    body = func[1]

    assert addr not in functions
    void = ir.VoidType()
    fnty = ir.FunctionType(void, [])
    func = ir.Function(module, fnty, name=str("0x%x" % addr))
    entry = func.append_basic_block (name='entry')
    functions[addr] = func
    first = True

    # Add starting blocks for each vertex
    for v in body['vertices']:
        add_vertexid (v, addr, func)

        # Add a branch to the first BB
        if first:
            first = False
            irb = ir.IRBuilder (entry)
            irb.branch (vertices [addr] [v['id']])

def convert_func (func, module, rax):
    #print (len(func))
    #print (func)

    addr = int (func[0])
    #print (addr)
    body = func[1]

    llvmfunc = functions[addr]

    for v in body['vertices']:
        #print (v)
        convert_vertex (v, addr, body, llvmfunc, rax)

    return func

def add_vertexid (v, funcaddr, llvmfunc):
    if funcaddr not in vertices:
        vertices[funcaddr] = {}
    assert v['id'] not in vertices[funcaddr]
    block = llvmfunc.append_basic_block (name=v['name'])
    vertices[funcaddr][v['id']] = block
    return block

def convert_vertex (v, funcaddr, body, llvmfunc, rax):
    block = vertices [funcaddr] [v['id']]
    irb = ir.IRBuilder (block)

    convert_stmts (v['stmts'], rax, irb)

    if not irb.block.is_terminated:

        edges = [e for e in body['edges'] if e['src'] == v['id']]

        if len(edges) == 0:
            irb.ret_void ()
        elif len(edges) == 1:
            e = edges[0]
            irb.branch (vertices [funcaddr] [e['dst']])
            #irb.branch (convert_vertexid (e['dst'], llvmfunc))
        elif len(edges) == 2:
            cond = convert_exp (edges[0] ['cond'], irb)
            irb.cbranch (cond,
                         vertices [funcaddr] [edges[0] ['dst']],
                         vertices [funcaddr] [edges[1] ['dst']])
        else:
            assert False

    return block

def convert_stmts(stmts, rax, irb=ir.IRBuilder ()):
    for stmt in stmts:
        convert_stmt (stmt, rax, irb)

def convert_stmt(stmt, rax, irb=ir.IRBuilder ()):
    #print (stmt)

    if stmt['op'] == "InsnStmt":
        return None
    elif stmt['op'] == "RegWriteStmt":
        dest = convert_var_noload (stmt['var'], irb)
        e = convert_exp (stmt['exp'], irb)
        return irb.store (e, dest)
    elif stmt['op'] == "MemWriteStmt":
        mem = M # ???
        addr = convert_exp (stmt['addr'], irb)
        val = convert_exp (stmt['exp'], irb)
        ptr = irb.inttoptr (irb.add (irb.ptrtoint (mem, addr.type),
                                     addr),
                            val.type.as_pointer ())
        return irb.store (val, ptr)
    elif stmt['op'] == "CallStmt":
        if stmt['calltype'] == "import":
            targetfunc = get_import_func (stmt ['file'], stmt ['func'])
            out = irb.call (targetfunc, [])
            return irb.store (out, rax)
        elif stmt['exp'] ['op'] == "constant":
            targetaddr = int (stmt['exp'] ['const'], 16)
            targetfunc = functions [targetaddr]
            return irb.call (targetfunc, [])
        else:
            irb.call (abort, [])
            return irb.unreachable ()
            # XXX: Should be able to mark this unreachable but we
            # can't right now because we try to add the branch which
            # fails
    else:
        assert False

def convert_var_noload (exp, irb=ir.IRBuilder ()):
    if exp['varname'] == 'M':
        return M

    if exp['varid'] not in vars:
        if exp['varname'] == 'M':
            typ = ir.PointerType (ir.IntType (8))
        else:
            typ = ir.IntType (int(exp['width']))

        # Use an alloca for temporaries
        if exp['varname'] == "":
            varname = "v%d" % int(exp['varid'])
            vars[exp['varid']] = irb.alloca (typ, name=varname)
        else:
            varname = exp['varname']
            vars[exp['varid']] = ir.GlobalVariable(module, typ, varname)

    return vars[exp['varid']]

def convert_exp(exp, irb=ir.IRBuilder ()):
    #print ("exp", exp)

    assert (exp['type'] == "exp")

    if exp['op'] == "constant":
        typ = ir.IntType (int(exp['width']))
        c = int(exp['const'], 16)
        return ir.Constant(typ, c)
    elif exp['op'] == "variable":
        return irb.load (convert_var_noload (exp, irb))
    elif exp['op'] == "read":
        children = list(map(lambda e: convert_exp(e, irb), exp['children']))
        addr = children[1]
        mem = irb.ptrtoint (children[0], addr.type)
        ptr = irb.inttoptr (irb.add (mem, addr), children[0].type)
        return irb.load (ptr)
    elif exp['op'] == "extract":
        low = int(exp['children'][0]['const'], 16)
        high = int(exp['children'][1]['const'], 16) - 1

        exp = convert_exp (exp['children'][2], irb)

        shift_exp = irb.lshr (exp, ir.Constant (exp.type, low))
        # Note: does not include high bit
        return irb.trunc (shift_exp, ir.IntType (high - low + 1))
    elif exp['op'] == "concat":
        finaltype = ir.IntType (int (exp['width']))
        widths = list(map(lambda e: int (e['width']), exp['children']))
        children = list(map(lambda e: convert_exp(e, irb), exp['children']))
        children = list(map(lambda e: irb.zext (e, finaltype), children))

        children = list(zip(widths, children))

        children.reverse ()

        bigexp = children[0][1] # don't care about the first width
        children = children[1:]
        for (width, exp) in children:
            const = ir.Constant (finaltype, width)
            bigexp = irb.shl (bigexp, const)
            bigexp = irb.or_ (bigexp, exp)
        return bigexp
    elif exp['op'] == "uextend":
        typ = ir.IntType (int (exp['width']))
        exp = convert_exp (exp['children'][1], irb)
        return irb.zext (exp, typ)
    elif exp['op'] == "zerop":
        assert (len(exp['children']) == 1)
        exp = convert_exp (exp['children'][0], irb)
        zero = ir.Constant (exp.type, 0)
        return irb.icmp_unsigned ('==', exp, zero)
    else:
        # Generic conversion when all children can simply be passed to
        # the corresponding builder method
        buildf = get_builder_op (exp['op'], irb)
        children = list(map(lambda e: convert_exp(e, irb), exp['children']))
        if exp['op'] in shifts:
            # ROSE has an annoying habit of using stupid types for constants
            children[0] = irb.zext (children[0], children[1].type)
            children.reverse ()
        if exp['op'] in reduction and len(exp['children']) > 2:
            # We have n > 2 children, but LLVM only wants 2
            return reduce (lambda a, b: buildf (a, b), children)
        else:
            # By specifying a name we detect mismatches in the number of arguments
            return buildf (*children, name="generic")

#double = ir.DoubleType()
#void = ir.VoidType()
#fnty = ir.FunctionType(void, [])
#func = ir.Function(module, fnty, name="test")
#block = func.append_basic_block(name="entry")

# exp1 = convert_exp(json.loads(conststr))
# exp2 = convert_exp(json.loads(conststr))
# irb = ir.IRBuilder(block)
# exp = irb.add(exp1, exp2)
# print(exp)

#exp = (convert_exp(json.loads(sys.stdin.read()), irb=ir.IRBuilder(block)))
convert_file(json.loads(sys.stdin.read()), module)
#print (exp)

#moduleref = binding.parse_assembly (str(module))

print (module)
#print (moduleref.as_bitcode ())

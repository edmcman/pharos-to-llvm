#!/usr/bin/python3

from functools import reduce
from llvmlite import ir, binding
import fileinput
import json
import sys

arie = True

vars = {}
exps = {}
vertices = {}
functions = {}
function_mem_reg = {}
import_functions = {}

STACK_SIZE = 10 * 1024 * 1024

module = ir.Module(name="test")
module.triple = "x86_64-apple-macosx10.14.0"
module.data_layout = "e-m:o-i64:64-f80:128-n8:16:32:64-S128"

bytetype = ir.IntType (8)
pointertype = bytetype.as_pointer ()
# integer type that is wide enough to store a pointer
pointerint = ir.IntType(64)
importfunctype = ir.FunctionType (ir.IntType (64), [])
voidfunctype = ir.FunctionType (ir.VoidType (), [])
abort = ir.Function (module, voidfunctype, "abort")
abort.attributes.add('noreturn')

def get_extract_func(high, low, bigwidth):
    smallwidth = high-low+1
    t = (smallwidth, bigwidth)

    if t not in get_extract_func.funcs:
        typ = ir.FunctionType (ir.IntType (smallwidth), [ir.IntType (64), ir.IntType (64), ir.IntType (bigwidth)])
        func = ir.Function (module, typ, "smt.extract.i%d.i%d" % (bigwidth, smallwidth))
        func.attributes.add("readnone")
        func.attributes.add("norecurse")
        func.attributes.add("nounwind")
        get_extract_func.funcs[t] = func

    return get_extract_func.funcs[t]
get_extract_func.funcs = {}

def get_concat_func(widths):
    widths = tuple(widths)
    if widths not in get_concat_func.funcs:
        total = sum (widths)
        typ = ir.FunctionType (ir.IntType (total), [ir.IntType (x) for x in widths])
        func = ir.Function (module, typ, "smt.concat" + "".join([".i%d" % x for x in widths]))
        func.attributes.add("readnone")
        func.attributes.add("norecurse")
        func.attributes.add("nounwind")
        get_concat_func.funcs [widths] = func

    return get_concat_func.funcs [widths]
get_concat_func.funcs = {}

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
    rax, _ = convert_var (file['regs'] ['rax_0'])
    rsp, _ = convert_var (file['regs'] ['rsp_0'])

    for func in file['functions'].items ():
        add_func (func, module)

    for func in file['functions'].items ():
        convert_func (func, module, rax)

    entry = ir.Function (module, voidfunctype, "main")
    entry.attributes.add('nounwind')
    entry.attributes.add('norecurse')

    #init = ir.Function (module, voidfunctype, "initialize_stuff")
    block = entry.append_basic_block("entry")
    irb = ir.IRBuilder (block)
    #irb.call (init, [])

    for var, key in file['regs'].items ():
        llvmvar, _ = convert_var (key)
        irb.store (ir.Constant (llvmvar.type.pointee, 0), llvmvar)

    stack = irb.alloca (ir.IntType (8), STACK_SIZE, name="stack")
    stack = irb.gep (stack, [ir.Constant (pointerint, STACK_SIZE - 8)], name="stack_top")
    irb.store (stack, rsp)
    irb.call (functions [int (file['sourcefunc'])], [])
    irb.ret_void ()

def get_import_func (file, func):
    tuple = (file, func)
    if tuple not in import_functions:
        func = ir.Function (module, importfunctype, name="%s!%s" % (file, func))
        func.attributes.add('inaccessiblememonly')
        import_functions [tuple] = func

    return import_functions [tuple]

def add_func (func, module):
    addr = int (func[0])
    body = func[1]

    assert addr not in functions
    void = ir.VoidType()
    fnty = ir.FunctionType(void, [])
    func = ir.Function(module, fnty, name=str("0x%x" % addr))
    func.linkage = 'internal'
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

    convert_stmts (v['stmts'], rax, irb, funcaddr)

    if not irb.block.is_terminated:

        edges = [e for e in body['edges'] if e['src'] == v['id']]

        if len(edges) == 0:
            irb.ret_void ()
        elif len(edges) == 1:
            e = edges[0]
            irb.branch (vertices [funcaddr] [e['dst']])
            #irb.branch (convert_vertexid (e['dst'], llvmfunc))
        elif len(edges) == 2:
            cond = convert_exp_bv (edges[0] ['cond'], irb)
            irb.cbranch (cond,
                         vertices [funcaddr] [edges[0] ['dst']],
                         vertices [funcaddr] [edges[1] ['dst']])
        else:
            assert False

    return block

def convert_stmts(stmts, rax, irb=ir.IRBuilder (), funcaddr=None):
    for stmt in stmts:
        convert_stmt (stmt, rax, irb, funcaddr)

# Should we convert the following regwritestmt as a write to a pointer or a write to a bitvector?
def should_convert_regwrite_as_pointer (stmt):
    if stmt ['var'] ['varname'] == "rsp_0":
        return True

    if stmt ['var'] ['varname'] == "":
        # Are we saving a snapshot of rsp?
        if stmt ['exp'] ['op'] == "variable" and stmt ['exp'] ['varname'] == "rsp_0":
            return True

    return False

def convert_stmt(stmt, rax, irb=ir.IRBuilder (), funcaddr=None):
    #print ("stmt", stmt)

    if stmt['op'] == "InsnStmt":
        return None
    elif stmt['op'] == "RegWriteStmt":

        if should_convert_regwrite_as_pointer (stmt):
            #print ("Converting as a ptr", stmt ['var'])
            e = convert_exp_ptr (stmt['exp'], irb, funcaddr)
        else:
            e = convert_exp_bv (stmt['exp'], irb, funcaddr)

        dest, _ = convert_var (stmt['var'], value=e, irb=irb)
        if dest is not None:
            assert e.type == dest.type.pointee
            return irb.store (e, dest)
        else:
            return None
    elif stmt['op'] == "MemWriteStmt":
        addr = convert_exp_ptr (stmt['addr'], irb, funcaddr)
        val = convert_exp_bv (stmt['exp'], irb, funcaddr)
        if arie:
            ptr = addr
            # Recast pointer if needed
            if ptr.type != val.type.as_pointer ():
                ptr = irb.bitcast (ptr, val.type.as_pointer ())
        else:
            assert False
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

def convert_var (exp, irb=ir.IRBuilder (), value=None):
    if exp['varname'] == 'M':
        # This shouldn't happen anymore
        assert False
        return M, lambda irb: irb.load (M)

    if exp['varid'] not in vars:
        if exp['varname'] == 'rsp_0':
            typ = pointertype
        else:
            typ = ir.IntType (int(exp['width']))

        # Use registers for temporaries
        if exp['varname'] == "":
            if value is not None:
                vars[exp['varid']] = None
                exps[exp['varid']] = lambda irb: value
            else:
                varname = "v%d" % int(exp['varid'])
                print ("WARNING: %s accessed before defined. This should not happen." % exp, file=sys.stderr)
                assert False
                vars[exp['varid']] = irb.alloca (typ, name=varname)
                exps[exp['varid']] = lambda irb: irb.load (vars[exp['varid']])
        else:
            varname = "pharos.reg." + exp['varname']
            var = ir.GlobalVariable(module, typ, varname)
            var.initializer = ir.Constant(typ, None)
            var.linkage = 'internal'
            vars[exp['varid']] = var
            if exp['varname'] == 'rsp_0':
                # Most of the time we don't want to access rsp as a pointer
                exps[exp['varid']] = lambda irb: irb.ptrtoint (irb.load (vars[exp['varid']]), ir.IntType (int (exp['width'])))
            else:
                exps[exp['varid']] = lambda irb: irb.load (vars[exp['varid']])

    return (vars[exp['varid']], exps[exp['varid']])

def convert_exp_ptr (exp, irb=ir.IRBuilder (), funcaddr=None):
    #print ("exp", exp)

    assert (exp['type'] == "exp")

    if exp['op'] == "add":
        ptr = convert_exp_ptr (exp ['children'] [0], irb, funcaddr)
        offset = convert_exp_bv (exp ['children'] [1], irb, funcaddr)
        return irb.gep (ptr, [offset])
    elif exp['op'] == "variable" and exp['varname'] == "rsp_0":
        v, _ = convert_var (exp, irb)
        return irb.load (v)
    else:
        bvexp = convert_exp_bv (exp, irb, funcaddr)
        return irb.inttoptr (bvexp, pointertype)

def convert_exp_bv (exp, irb=ir.IRBuilder (), funcaddr=None, cache=None):
    if cache is None:
        cache = {}
    assert (exp['type'] == "exp")

    def convert_exp_bv_int (exp, irb, funcaddr):
        if exp['op'] == "unknown":
            return ir.Constant (ir.IntType (int (exp['width'])), ir.Undefined)
        elif exp['op'] == "constant":
            typ = ir.IntType (int(exp['width']))
            c = int(exp['const'], 16)
            return ir.Constant(typ, c)
        elif exp['op'] == "variable":
            _, f = convert_var (exp, irb)
            return f (irb)
        elif exp['op'] == "read":
            addr = convert_exp_ptr (exp ['children'] [1], irb, funcaddr)
            if arie:
                ptr = addr
                # Bitcast pointer if needed
                if ptr.type.pointee.width != exp['width']:
                    ptr = irb.bitcast (ptr, ir.IntType (int (exp['width'])).as_pointer ())
            else:
                assert False
                mem = irb.ptrtoint (children[0], addr.type)
                ptr = irb.inttoptr (irb.add (mem, addr), children[0].type)
            return irb.load (ptr)
        elif exp['op'] == "extract":
            low = int(exp['children'][0]['const'], 16)
            high = int(exp['children'][1]['const'], 16) - 1

            newexp = convert_exp_bv (exp['children'][2], irb, funcaddr, cache)

            if arie:
                f = get_extract_func (high, low, newexp.type.width) #exp['children'][2]['width'])
                lowc = ir.Constant (ir.IntType (64), low)
                highc = ir.Constant (ir.IntType (64), high)
                return irb.call (f, [lowc, highc, newexp])
            else:
                shift_exp = irb.lshr (newexp, ir.Constant (newexp.type, low))
                # Note: does not include high bit
                return irb.trunc (shift_exp, ir.IntType (high - low + 1))
        elif exp['op'] == "concat":
            finaltype = ir.IntType (int (exp['width']))
            widths = list(map(lambda e: int (e['width']), exp['children']))
            children = list(map(lambda e: convert_exp_bv(e, irb, funcaddr, cache), exp['children']))

            if arie:
                f = get_concat_func (widths)
                return irb.call (f, children)
            else:

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
            exp = convert_exp_bv (exp['children'][1], irb, funcaddr, cache)
            return irb.zext (exp, typ)
        elif exp['op'] == "zerop":
            assert (len(exp['children']) == 1)
            exp = convert_exp_bv (exp['children'][0], irb, funcaddr, cache)
            zero = ir.Constant (exp.type, 0)
            return irb.icmp_unsigned ('==', exp, zero)
        else:
            # Generic conversion when all children can simply be passed to
            # the corresponding builder method
            buildf = get_builder_op (exp['op'], irb)
            children = list(map(lambda e: convert_exp_bv (e, irb, funcaddr, cache), exp['children']))
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

    if str (exp) not in cache:
        cache [str(exp)] = convert_exp_bv_int (exp, irb, funcaddr)

    return cache [str(exp)]



convert_file(json.loads("\n".join(f for f in fileinput.input())), module)
print (module)

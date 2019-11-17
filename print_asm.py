from functools import reduce
from llvmlite import ir, binding
import fileinput
import json
import sys
import io
import ctypes

def is_flag(name):
    flags = ['pf_0', 'zf_0', 'af_0', 'cf_0', 'of_0', 'sf_0']
    return name in flags

class AsmPrinter(object):
    def __init__(self, program, file, with_flags = False):
        self._program = program
        self._file = file
        self._indent = 0
        self._with_flags = with_flags


    def indent(self, num = 2):
        self._indent += num
    def outdent(self, num = 2):
        self.indent(-num)
        assert(self._indent >= 0)
    def write(self, str):
        self._file.write(' '*self._indent)
        self._file.write(str)
    def writeln(self, str = ''):
        self.write(str)
        self._file.write('\n')
        self._file.flush()

    def run(self):
        for fn in program['functions']:
            self.print_fn(fn, program['functions'][fn])

    def print_fn(self, name, body):
        self.writeln()
        self.writeln('functon {}:'.format(name))
        self.indent()
        for bb in body['vertices']:
            self.print_bb(bb)
            self.writeln()
        self.outdent()

    def print_bb(self, bb):
        self.write('{}:'.format(bb['name']))
        self.indent()
        dirty = False
        for s in bb['stmts']:
            nl = self.print_stmt(s)
            dirty = dirty or nl

        if not dirty:
            self.writeln()
        self.outdent()

    def print_stmt(self, s):
        if s['op'] == 'InsnStmt':
            return self.print_InsnStmt(s)
        elif s['op'] == 'RegWriteStmt':
            return self.print_RegWriteStmt(s)
        elif s['op'] == 'MemWriteStmt':
            return self.print_MemWriteStmt(s)
        elif s['op'] == 'CallStmt':
            return self.print_CallStmt(s)
        else:
            self.writeln(s['op'])
            return True
        return False

    def print_InsnStmt(self, s):
        self.writeln(s['asm'])
        return True
    def print_RegWriteStmt(self, s):
        var = self.var_str(s['var'])
        if not self._with_flags and is_flag(var):
            return False
        exp = self.exp_str(s['exp'])
        self.writeln('{} := {}'.format(var, exp))
        return True

    def print_CallStmt(self, s):
        self.writeln('{} {}'.format(s['op'], s['calltype']))
        return True

    def print_MemWriteStmt(self, s):
        addr = self.addr_str(s['addr'])
        exp = self.exp_str(s['exp'])
        self.writeln("MEM[{}] := {}".format(addr, exp))

    def addr_str(self, addr):
        out = io.StringIO()
        self.print_addr(addr, out)
        return out.getvalue()

    def print_addr(self, addr, out):
        assert (addr['type'] == 'exp')
        op = addr['op']
        if op == 'variable':
            out.write(self.var_str(addr))
        elif op == 'constant':
            out.write(self.const_str(addr))
        elif op == 'add':
            kids = addr['children']
            assert(len(kids) == 2)
            self.print_addr(kids[0], out)
            out.write(' + ')
            self.print_addr(kids[1], out)

    def var_str(self, var):
        if var['varname'] != '':
            return str(var['varname'])
        else:
            return 'v{}'.format(var['varid'])

    def const_str(self, v):
        val = int(v['const'], 16)

        if v['width'] == '64':
            val = ctypes.c_int64(val)
            val = val.value
        elif v['width'] == '32':
            val = ctypes.c_int32(val)
            val = val.value
        else:
            pass
        return str(val)

    def exp_str(self, v):
        out = io.StringIO()
        self.print_exp(v, out)
        return out.getvalue()

    def print_exp(self, v, out):
        op = v['op']
        if op == 'variable':
            out.write(self.var_str(v))
        elif op == 'constant':
            out.write(self.const_str(v))
        elif op == 'add':
            kids = v['children']
            assert(len(kids) == 2)
            self.print_exp(kids[0], out)
            out.write(' + ')
            self.print_exp(kids[1], out)
        elif op == 'read':
            array, idx = v['children']
            self.print_exp(array, out)
            out.write('[')
            self.print_exp(idx, out)
            out.write(']')
        elif op == 'concat':
            kids = v['children']
            kids = [self.exp_str(k) for k in kids]
            out.write(' :: '.join(kids))
        elif op == 'extract':
            low, high, body = v['children']
            self.print_exp(body, out)
            out.write('[{}:{}]'.format(int(low['const']), int(high['const'])))

        else:
            out.write(str(v))

program = json.loads("\n".join(f for f in fileinput.input()))
printer = AsmPrinter(program, sys.stdout)
printer.run()

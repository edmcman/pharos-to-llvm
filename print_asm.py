from functools import reduce
from llvmlite import ir, binding
import fileinput
import json
import sys

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
        self.writeln('{} := {}'.format(var, ''))
        return True

    def print_CallStmt(self, s):
        self.writeln('{} {}'.format(s['op'], s['calltype']))
        return True

    def print_MemWriteStmt(self, s):
        addr = self.addr_str(s['addr'])
        self.writeln("MEM[{}] := {}".format(addr, ''))

    def addr_str(self, addr):
        return 'addr'
    def var_str(self, var):
        if var['varname'] != '':
            return str(var['varname'])
        else:
            return 'v{}'.format(var['varid'])

program = json.loads("\n".join(f for f in fileinput.input()))
printer = AsmPrinter(program, sys.stdout)
printer.run()

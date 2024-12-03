# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

import sys
import copy

import io
import z3

from .undef_visitor import UndefVisitor
from . import ast, int as interpreter
from functools import reduce

from collections import deque


class SymState(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.env = dict()
        # path condition
        self.path = list()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()

        # true if this is an error state
        self._is_error = False
        self.n_loops = dict()
        self.bit_vec = z3.BitVecSort(32)

    def add_pc(self, *exp):
        """Add constraints to the path condition"""
        self.path.extend(exp)
        self._solver.append(exp)
        # for ex in exp:
        #     if isinstance(ex, z3.BoolRef):
        #         self._solver.append(z3.is_true(ex))
        #     else:
        #         self._solver.append(ex)

    def push(self):
        self._solver.push()

    def pop(self):
        self._solver.pop()
        self.path.pop()

    def use_deep_copy_env(self):
        new_env = copy.deepcopy(self.env)
        self.env = new_env

    def is_error(self):
        return self._is_error

    def mk_error(self):
        self._is_error = True

    def is_empty(self):
        """Check whether the current symbolic state has any concrete states"""
        res = self._solver.check()
        return res == z3.unsat

    def pick_concerete(self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check()
        if res != z3.sat:
            return None
        model = self._solver.model()
        st = interpreter.State()
        for (k, v) in self.env.items():
            st.env[k] = model.eval(v)
        return st

    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = SymState()
        child.env = dict(self.env)
        # child.add_pc(*self.path)
        child.path.extend(self.path)
        child._solver.add(self._solver.assertions())
        for key, value in self.n_loops.items():
            child.n_loops[key] = value

        return (self, child)

    def __repr__(self):
        return str(self)

    def to_smt2(self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2()

    def __str__(self):
        buf = io.StringIO()
        for k, v in self.env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('pc_length: ')
        buf.write(str(len(self.path)))
        buf.write('\n')
        buf.write('pc: ')
        buf.write(str(self.path))
        buf.write('\n\n')

        return buf.getvalue()


class SymExec(ast.AstVisitor):
    def __init__(self):
        pass

    def run(self, ast, state):
        # set things up and
        # call self.visit (ast, state=state)
        return self.visit(ast, state=state)

    def visit_IntVar(self, node, *args, **kwargs):
        return kwargs['state'].env[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        return z3.BitVecVal(int(node.val), 1)

    def visit_IntConst(self, node, *args, **kwargs):
        return z3.BitVecVal(node.val, 32)

    def visit_RelExp(self, node, *args, **kwargs):
        lhs = self.visit(node.arg(0), *args, **kwargs)
        rhs = self.visit(node.arg(1), *args, **kwargs)
        if node.op == "<=":
            return z3.ULE(lhs, rhs)
        if node.op == "<":
            return z3.ULT(lhs, rhs)
        if node.op == "=":
            return lhs == rhs
        if node.op == ">=":
            return z3.UGE(lhs, rhs)
        if node.op == ">":
            return z3.UGT(lhs, rhs)

    def visit_BExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        if node.op == "not":
            assert node.is_unary()
            assert len(kids) == 1
            # return z3.Z3_mk_bvnot(kwargs['state'].bit_vec.ctx_ref(), kids[0])
            return ~kids[0]

        fn = None
        base = None
        if node.op == "and":
            # fn = lambda x, y: z3.Z3_mk_bvand(kwargs['state'].bit_vec.ctx_ref(), x, y)
            fn = lambda x, y: x & y
            base = z3.Z3_mk_true(kwargs['state'].bit_vec.ctx_ref())
        elif node.op == "or":
            # fn = lambda x, y: z3.Z3_mk_bvor(kwargs['state'].bit_vec.ctx_ref(), x, y)
            fn = lambda x, y: x | y
            base = z3.Z3_mk_false(kwargs['state'].bit_vec.ctx_ref())

        assert fn is not None
        return reduce(fn, kids, base)

    def visit_AExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]

        fn = None

        if node.op == "+":
            fn = lambda x, y: x + y

        elif node.op == "-":
            fn = lambda x, y: x - y

        elif node.op == "*":
            fn = lambda x, y: x * y

        elif node.op == "/":
            fn = lambda x, y: x / y

        assert fn is not None
        return reduce(fn, kids)

    def visit_SkipStmt(self, node, *args, **kwargs):
        return [kwargs['state']]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        #print(self.states[0])
        return [kwargs['state']]

    def visit_AsgnStmt(self, node, *args, **kwargs):
        st = kwargs["state"]
        value = self.visit(node.rhs, *args, **kwargs)
        st.env[node.lhs.name] = z3.BitVec(node.lhs.name, 32)
        st.add_pc(st.env[node.lhs.name] == value)
        return [st]

    def visit_IfStmt(self, node, *args, **kwargs):
        cond = self.visit(node.cond, *args, **kwargs)

        st = kwargs['state']
        env = st.env

        #og, new_st = st.fork()
        # nkwargs = dict(kwargs)
        # nkwargs['state'] = og

        states = []

        st.push()
        st.add_pc(cond)
        st.use_deep_copy_env()
        if not st.is_empty():
            states.extend(self.visit(node.then_stmt, *args, **kwargs))

        st.pop()

        st.env = env

        st.push()
        st.add_pc(z3.Not(cond))
        st.use_deep_copy_env()
        if not st.is_empty():
            if node.has_else():
                states.extend(self.visit(node.else_stmt, *args, **kwargs))
            else:
                _, new_st = st.fork()
                states.append(new_st)
        st.pop()

        return states

    def visit_WhileInvStmt(self, node, *args, **kwargs):
        cond = self.visit(node.cond, *args, **kwargs)
        inv = self.visit(node.inv, *args, **kwargs)

        st = kwargs['state']
        # body_st, assert_st = kwargs['state'].fork()
        st.push()
        st.add_pc(z3.Not(inv))
        if not st.is_empty():
            print("Assertion failed before loop:", st.pick_concerete(), "Inv:", inv)
            st.pop()
            return
        st.pop()

        undef_visitor = UndefVisitor()
        undef_visitor.check(node.body)
        vars = undef_visitor.get_defs()
        for v in vars:
            st.env[v.name] = z3.BitVec(v.name, 32)

        inv = self.visit(node.inv, *args, **kwargs)
        st.add_pc(inv)
        st.push()
        # _, new_st = body_st.fork()
        st.add_pc(cond)
        if not st.is_empty():
            states = self.visit(node.body, *args, **kwargs)
            for s in states:
                inv = self.visit(node.inv, *args, state=s)
                s.add_pc(z3.Not(inv))

                if not s.is_empty():
                    print("Assertion failed after body:", s.pick_concerete(), "Inv:", inv)

            #No need to return all the states because assume false is the last statement in the body

        st.pop()
        st.add_pc(z3.Not(cond))
        if not st.is_empty():
            return [st]

    def visit_WhileNoInvStmt(self, node, *args, **kwargs):
        st = kwargs['state']
        node_literal = str(node)
        states = set()
        if st.n_loops.get(node_literal) is None:
            st.n_loops[node_literal] = 0

        cond = self.visit(node.cond, *args, **kwargs)

        # st, false_st = st.fork()

        env = st.env
        st.push()
        st.use_deep_copy_env()
        st.add_pc(cond)

        if not st.is_empty():
            st.n_loops[node_literal] += 1
            if st.n_loops[node_literal] <= 10:
                # execute the body
                body_states = self.visit(node.body, *args, **kwargs)
                for s in body_states:
                    # execute the loop again
                    loop_states = self.visit(node, *args, state=s)
                    states.update(loop_states)

        st.pop()

        # No loop
        st.push()
        st.env = env
        st.use_deep_copy_env()

        st.add_pc(z3.Not(cond))
        if not st.is_empty():
            del st.n_loops[node_literal]
            _, new_st = st.fork()
            states.add(new_st)

        st.pop()
        return list(states)

    def visit_WhileStmt(self, node, *args, **kwargs):
        if node.inv is None:
            return self.visit_WhileNoInvStmt(node, *args, **kwargs)
        else:
            return self.visit_WhileInvStmt(node, *args, **kwargs)

    def visit_AssertStmt(self, node, *args, **kwargs):
        # Don't forget to print an error message if an assertion might be violated
        cond = self.visit(node.cond, *args, **kwargs)
        # st, new_st = kwargs['state'].fork()

        st = kwargs['state']
        st.push()
        st.add_pc(z3.Not(cond))
        if not st.is_empty():
            st.mk_error()
            print("Assertion failed:", st.pick_concerete(), "Node:", node)

        st.pop()

        st.add_pc(cond)
        if not st.is_empty():
            return [st]

    def visit_AssumeStmt(self, node, *args, **kwargs):
        cond = self.visit(node.cond, *args, **kwargs)
        kwargs['state'].add_pc(cond)
        if not kwargs['state'].is_empty():
            return [kwargs['state']]

    def visit_HavocStmt(self, node, *args, **kwargs):
        for v in node.vars:
            # assign 0 as the default value
            kwargs["state"].env[v.name] = z3.BitVec(v.name, 32)
        return [kwargs["state"]]

    def visit_StmtList(self, node, *args, **kwargs):
        nkwargs = dict(kwargs)
        states = [kwargs['state']]
        temp = []

        for stmt in node.stmts:
            for st in states:
                nkwargs["state"] = st
                ns = self.visit(stmt, *args, **nkwargs)
                if ns is not None:
                    temp.extend(ns)
            states = temp
            temp = []
        return states


def _parse_args():
    import argparse
    ap = argparse.ArgumentParser(prog='sym',
                                 description='WLang Interpreter')
    ap.add_argument('in_file', metavar='FILE',
                    help='WLang program to interpret')
    args = ap.parse_args()
    return args


def main():
    args = _parse_args()
    prg = ast.parse_file(args.in_file)
    st = SymState()
    sym = SymExec()

    states = sym.run(prg, st)
    if states is None:
        print('[symexec]: no output states')
    else:
        count = 0
        for out in states:
            count = count + 1
            print('[symexec]: symbolic state reached')
            print(out)
        print('[symexec]: found', count, 'symbolic states')
    return 0


if __name__ == '__main__':
    sys.exit(main())

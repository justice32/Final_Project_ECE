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

import unittest

from . import ast, sym


class TestSym (unittest.TestCase):
    def test_one(self):
        prg1 = "havoc x; if (1 > 0) then x := 11 else x := 12; if (2 > 3) then x := 99 else x := 100; assume x = 10; assert x < 15"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_two(self):
        prg1 = "havoc x; x := 100; while (x > 50) do { havoc y; y := 5; while (y > 0) do { x := x - 1; y := y - 1 } }"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_three(self):
        prg1 = "havoc x; if (1 > 0) then if (2 > 3) then x := 99 else x := 100 else x := 12; assume x > 10; assert x > 15"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_four(self):
        prg1 = "havoc x, y, z; x := 15; y := -1; z := 100; if ((x < 0 or z >= 0) and not y <= 7) then x := 11 else x := 12; if (2 > 3) then x := 99 else x := 100; assume x > 10; assert x > 15"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_five(self):
        prg1 = "havoc x; if x * 1 = 0 and true then x := 11 else skip; if x + 1 = 12 and 11 / x = 1 then x := 99"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 3)

    def test_six(self):
        prg1 = "havoc x; print_state; assert x > 10 or 10 > 5; y := 10 / 5"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_seven(self):
        prg1 = "havoc x; x := 100; while (x > 50) do { havoc y; y := 5; while (y > 0) do { while (true) do { while (x < y) do { x := x - 1; y := y - 1 } } } }; while (x > 1) do { havoc z; z := 19; while (z < 100) do { havoc t; t := 1000; while (t > 500) do { x := x - 1; t := t + 1 } } }"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_q4b(self):
        prg1 = "havoc x, y; assume y >= 0; c := 0; r := x; while c < y inv r - c = x and c <= y do { r := r + 1; c := c + 1 }; assert r = x + y"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_nine(self):
        prg1 = "havoc x, y; x:= 0; y := 0; while x < 10 inv y = 0 do {x := x + 1}"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_ten(self):
        prg1 = "havoc x, y; x:= 0; y := 0; while x = 10 inv y = 0 do {x := x + 1}"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_eleven(self):
        prg1 = "havoc x, y; x:= 0; y := 1; while x = 10 inv y = 0 do {x := x + 1}; assert 10 > 5; assert 10 < 5"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_q4d(self):
        prg1 = "havoc x, y; assume y >= 0; c := 0; r := x; while c < y inv r = x + c * 2 and c <= y do { r := r + 2; c := c + 1 }; assert r = x + y * 2"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)
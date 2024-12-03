import unittest

from . import ast, sym_scopes_bit_vec as sym


class TestSym (unittest.TestCase):
    def test_one(self):
        prg1 = "havoc x; if (1 > 0) then x := 11 else x := 12; if (2 > 3) then x := 99 else x := 100; assume x = 10; assert x < 15"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_two(self):
        prg1 = "havoc x; while (x > 50) do { havoc y; y := 5; while (y > 0) do { x := x - 1; y := y - 1 } }"
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
        prg1 = "havoc x, y, z; x := 15; y := -1; z := 100; if x < 0 then x := 11 else x := 12; if 2 > 3 then x := 99 else x := 100; assume x > 10; assert x > 15"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_five(self):
        prg1 = "havoc x; if x * 1 = 0 then x := 11 else skip; if 11 / x = 1 then x := 99"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 4)

    def test_six(self):
        prg1 = "havoc x; print_state; assert x > 10; y := 10 / 5"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    # def test_seven(self):
    #     prg1 = "havoc x; x := 100; while (x > 50) do { havoc y; y := 5; while (y > 0) do { while (true) do { while (x < y) do { x := x - 1; y := y - 1 } } } }; while (x > 1) do { havoc z; z := 19; while (z < 100) do { havoc t; t := 1000; while (t > 500) do { x := x - 1; t := t + 1 } } }"
    #     ast1 = ast.parse_string(prg1)
    #     engine = sym.SymExec()
    #     st = sym.SymState()
    #     out = [s for s in engine.run(ast1, st)]
    #     self.assertEquals(len(out), 1)

    def test_q4b(self):
        prg1 = "havoc x, y; assume y >= 0; c := 0; r := x; while c < y inv r - c = x do { r := r + 1; c := c + 1 }; assert r = x + y"
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
        prg1 = "havoc x, y; x:= 0; y := 1; while x = 10 inv y = -1 do {x := x + 1}; assert 10 > 5; assert 10 < 5"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_q4d(self):
        prg1 = "havoc x, y; assume y >= 0; c := 0; r := x; while c < y inv r = x + c * 2 do { r := r + 2; c := c + 1 }; assert r = x + y * 2"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_twelve(self):
        prg1 = "havoc x, y; x := 1; if x < 0 then print_state"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_thirteen(self):
        prg1 = "havoc x, y; x := 1; assert x = 1; assert y < 0"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_fourteen(self):
        prg1 = "havoc x, y; x:= 0; y := 0; while x < 1 inv y = 0 do {x := x + 1}"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_fifteen(self):
        prg1 = "havoc x, y; x:= 0; y := 0; while x < 2 do {x := x + 1}"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_sixteen(self):
        prg1 = "havoc x, y; x := 0; y:= 0; while x < 1 do x := x + 1; assert x = 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)

    def test_seventeen(self):
        prg1 = "havoc x, y; x := 0; y:= 0; while x < 1 and true or 10 / 5 = 2 do x := x + 1; assert x = 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_eighteen(self):
        prg1 = "havoc x, y; while not true or x <= 1 do x := x + 1; assert x = 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)
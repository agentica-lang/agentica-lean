import Analysis from "std/analysis"
import Lean from "lean"

def test_writes_branches_and_short_circuits() -> Result[Void]
  source = <<~AGC
    def pick(at: Int, flag: Bool) -> Result[Int]
      if at > 0 and flag
        return ok(at)
      elsif at == 0
        return error("zero")
      else
        return error("at \#{at}", kind: "argument")
      end
    end
  AGC
  text = try translate(source, ["pick"])
  Test.eq(
    body(text),
    <<~LEAN,
    def pick («at» : AInt) (flag : Bool) : M (Result AInt) := do
      if (if Agentica.AInt.gt «at» (Agentica.AInt.ofInt 0) then flag else false) then
        return .ok «at»
      else
        if Agentica.AInt.eq «at» (Agentica.AInt.ofInt 0) then
          return .error { message := "zero" }
        else
          return .error { kind := "argument", message := "at " ++ Agentica.String.from_int «at» }
  LEAN
  )
end

def test_binds_try_inside_an_expression() -> Result[Void]
  source = <<~AGC
    def half(n: Int) -> Result[Int]
      return error("odd") if n.bit_and(1) == 1

      ok(n.shift_right(1))
    end

    def quarter(n: Int) -> Result[Int] = ok((try half(n)).shift_right(1))
  AGC
  text = try translate(source, ["quarter"])
  Test.assert(
    text.include?(
      <<~LEAN,
    def quarter (n : AInt) : M (Result AInt) := do
      match ← Agentica.Out.half n with
      | .error e => return .error e
      | .ok t1 =>
        let t2 ← Agentica.AInt.shift_right t1 (Agentica.AInt.ofInt 1)
        return .ok t2
  LEAN
    ),
    text,
  )
end

def test_runs_named_arguments_in_source_order() -> Result[Void]
  source = <<~AGC
    def sub2(a: Int, b: Int) -> Int = a - b

    def use(x: Int, data: Bytes) -> Int = sub2(b: x + 9223372036854775807, a: data[5])
  AGC
  text = try translate(source, ["use"])
  Test.assert(
    text.include?(
      <<~LEAN,
    def use (x : AInt) (data : Bytes) : M AInt := do
      let t1 ← Agentica.AInt.add x (Agentica.AInt.ofInt 9223372036854775807)
      let t2 ← Agentica.Bytes.at data (Agentica.AInt.ofInt 5)
      Agentica.Out.sub2 t2 t1
  LEAN
    ),
    text,
  )
end

def test_keeps_its_names_apart_from_the_source_names() -> Result[Void]
  source = <<~AGC
    def pure(b: Bool) -> Bool = !b

    def t1(n: Int) -> Result[Int] = ok(n)

    def f(a: Bool, n: Int, m: Int) -> Result[Bool]
      x = pure(a)
      y = try t1(n)
      ok(x and y > m)
    end

    def g(window: Bool) -> Bool = window(window)

    def window(w: Bool) -> Bool = w
  AGC
  text = try translate(source, ["f", "g"])
  try Test.assert(text.include?("let x ← Agentica.Out.pure a\n"), text)
  try Test.assert(text.include?("match ← Agentica.Out.t1 n with\n"), text)
  try Test.assert(!text.include?("let t1 "), text)
  Test.assert(text.include?("Agentica.Out.window window\n"), text)
end

def test_writes_try_in_a_condition_inside_its_arm() -> Result[Void]
  source = <<~AGC
    def pos(n: Int) -> Result[Int]
      return error("neg") if n < 0

      ok(n)
    end

    def cond_try(n: Int) -> Result[Int]
      if (try pos(n)) > 1
        return ok(1)
      end
      ok(2)
    end
  AGC
  text = try translate(source, ["cond_try"])
  Test.assert(
    text.include?(
      <<~LEAN,
    def cond_try (n : AInt) : M (Result AInt) := do
      match ← Agentica.Out.pos n with
      | .error e => return .error e
      | .ok t1 =>
        if Agentica.AInt.gt t1 (Agentica.AInt.ofInt 1) then
          return .ok (Agentica.AInt.ofInt 1)
        return .ok (Agentica.AInt.ofInt 2)
  LEAN
    ),
    text,
  )
end

def test_wraps_an_int_interpolation_as_an_argument() -> Result[Void]
  source = <<~AGC
    def h(s: String) -> String = s

    def k(n: Int) -> String = h("\#{n}")
  AGC
  text = try translate(source, ["k"])
  Test.assert(text.include?("  Agentica.Out.h (Agentica.String.from_int n)\n"), text)
end

def test_refuses_an_error_with_a_code() -> Result[Void]
  refused("def m(n: Int) -> Result[Int] = error(\"x\", code: 3)\n", ["m"], "code, details or cause")
end

def test_refuses_try_on_the_right_of_or() -> Result[Void]
  source = <<~AGC
    def g(n: Int) -> Result[Int] = ok(n)

    def f(a: Bool, n: Int) -> Result[Bool] = ok(a or (try g(n)) > 0)
  AGC
  refused(source, ["f"], "try on the right of or")
end

def test_refuses_an_impure_function() -> Result[Void]
  source = <<~AGC
    def shout(n: Int) -> Int
      puts(n)
      n
    end
  AGC
  refused(source, ["shout"], "shout: not pure")
end

def test_refuses_recursion() -> Result[Void]
  source = <<~AGC
    def down(n: Int) -> Int
      return 0 if n <= 0

      down(n - 1)
    end
  AGC
  refused(source, ["down"], "down: recursion")
end

def test_refuses_a_loop() -> Result[Void]
  source = <<~AGC
    def count(n: Int) -> Int
      i = 0
      while i < n
        i += 1
      end
      i
    end
  AGC
  refused(source, ["count"], "is a later step")
end

private

def translate(source: String, roots: List[String]) -> Result[String]
  path = "translator_fixture.agc"
  session = (
    Analysis.workspace()
    |> Analysis.open()
    |> Analysis.update(path, source)
  )

  found = try Analysis.bodies(session, path)
  Lean.translate(Lean.Job(source: path, roots: roots, path: "Out.lean", namespace: "Agentica.Out"), found)
end

def body(text: String) -> String
  start = text.index_of("def ").unwrap_or(0)
  stop = text.index_of("\n\nend Agentica.Out").unwrap_or(text.length)
  text.slice(start, stop - start) + "\n"
end

def refused(source: String, roots: List[String], part: String) -> Result[Void]
  case translate(source, roots)
    ok(text) -> error("translated:\n#{text}")
    error(e) -> Test.assert(e.message.include?(part), e.message)
  end
end

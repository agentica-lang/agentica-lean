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
      match ← half n with
      | .error e => return .error e
      | .ok t1 =>
        let t2 ← Agentica.AInt.shift_right t1 (Agentica.AInt.ofInt 1)
        return .ok t2
  LEAN
    ),
    text,
  )
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

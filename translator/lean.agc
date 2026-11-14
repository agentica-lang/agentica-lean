## Translates the pure functions of an Agentica file to Lean 4, from the typed tree of `Analysis.bodies`. The shape of
## the output is in `docs/translator.md`; a function outside the subset is refused with the reason.

import Analysis from "std/analysis"

## What to translate: the functions `roots` of the file `source` and every function of that file they call, into the
## module `namespace` (one Lean file), which is inside `Agentica` so that the prelude types keep their short names.
struct Job
  source: String
  roots: List[String]
  path: String
  namespace: String
end

## Translates `job` from `found`, the answer of `Analysis.bodies` for `job.source`: the text of the Lean file.
def translate(job: Job, found: Analysis.Bodies) -> Result[String]
  return error("the namespace #{job.namespace} is not inside Agentica") if !job.namespace.start_with?("Agentica.")

  functions = found.functions.reduce({}) do |m: Map[String, Analysis.Body], f| m.put(f.linked, f) end
  order = try ordered(functions, job.roots)
  modules: Set[String] = Set.new(["Agentica.Prelude.Result", "Agentica.Prelude.RuntimeError"])
  defs: List[String] = []
  for name in order
    body = functions[name]
    out = try function_text(functions, body, job.namespace)
    defs = defs.push(out.text)
    modules = modules.union(out.modules)
  end
  imports = modules.to_a.sort.map { |m| "import #{m}" }.join("\n")
  ok(
    header(job) +
    imports +
    "\n\n" +
    doc(job) +
    "namespace #{job.namespace}\n\n" +
    defs.join("\n\n") +
    "\n\nend #{job.namespace}\n",
  )
end

private

ARITH = "Agentica.Prelude.Int.Arith"
COMPARE = "Agentica.Prelude.Int.Compare"
BITS = "Agentica.Prelude.Int.Bits"
BUILTINS = {
  "Int.shift_left": Builtin(lean: "Agentica.AInt.shift_left", halts: true, module: "Agentica.Prelude.Int.ShiftLeft"),
  "Int.shift_right": Builtin(
    lean: "Agentica.AInt.shift_right",
    halts: true,
    module: "Agentica.Prelude.Int.ShiftRight",
  ),
  "Int.shift_right_unsigned": Builtin(
    lean: "Agentica.AInt.shift_right_unsigned",
    halts: true,
    module: "Agentica.Prelude.Int.ShiftRightUnsigned",
  ),
  "Int.bit_and": Builtin(lean: "Agentica.AInt.bit_and", halts: false, module: BITS),
  "Int.bit_or": Builtin(lean: "Agentica.AInt.bit_or", halts: false, module: BITS),
  "Int.bit_xor": Builtin(lean: "Agentica.AInt.bit_xor", halts: false, module: BITS),
  "Int.bit_not": Builtin(lean: "Agentica.AInt.bit_not", halts: false, module: BITS),
  "Int.to_s": Builtin(lean: "Agentica.String.from_int", halts: false, module: "Agentica.Prelude.String.FromInt"),
  "Bytes.length": Builtin(lean: "Agentica.Bytes.length", halts: false, module: "Agentica.Prelude.Bytes"),
  "Bytes.at": Builtin(lean: "Agentica.Bytes.at", halts: true, module: "Agentica.Prelude.Bytes"),
  "Bytes.from_list": Builtin(
    lean: "Agentica.Bytes.from_list",
    halts: false,
    module: "Agentica.Prelude.Bytes.FromList",
  ),
  "Result.unwrap!": Builtin(lean: "Agentica.Result.unwrap!", halts: true, module: "Agentica.Prelude.Result.Unwrap"),
}
BYTES_PLUS = Builtin(lean: "Agentica.Bytes.plus", halts: false, module: "Agentica.Prelude.Bytes.Plus")
NEG = Builtin(lean: "Agentica.AInt.neg", halts: true, module: "Agentica.Prelude.Int.Neg")
OPERATORS = {
  "+": Builtin(lean: "Agentica.AInt.add", halts: true, module: ARITH),
  "-": Builtin(lean: "Agentica.AInt.sub", halts: true, module: ARITH),
  "==": Builtin(lean: "Agentica.AInt.eq", halts: false, module: COMPARE),
  "!=": Builtin(lean: "Agentica.AInt.ne", halts: false, module: COMPARE),
  "<": Builtin(lean: "Agentica.AInt.lt", halts: false, module: COMPARE),
  "<=": Builtin(lean: "Agentica.AInt.le", halts: false, module: COMPARE),
  ">": Builtin(lean: "Agentica.AInt.gt", halts: false, module: COMPARE),
  ">=": Builtin(lean: "Agentica.AInt.ge", halts: false, module: COMPARE),
}
KEYWORDS = Set.new([
  "abbrev", "at", "attribute", "axiom", "by", "calc", "catch", "class", "decreasing_by", "def", "deriving", "do",
  "else", "end", "example", "export", "extends", "finally", "for", "from", "fun", "have", "hiding", "if", "import",
  "in", "include", "inductive", "infix", "infixl", "infixr", "instance", "lemma", "let", "local", "macro",
  "macro_rules", "match", "mutual", "mut", "namespace", "noncomputable", "nofun", "nomatch", "notation", "omit",
  "opaque", "open", "partial", "postfix", "prefix", "private", "protected", "public", "renaming", "return", "rfl",
  "section", "set_option", "show", "structure", "suffices", "syntax", "termination_by", "then", "theorem", "try",
  "universe", "unless", "variable", "where", "with",
])

# A Lean term and the generator after it: `atom` when it needs no parentheses as an argument, `hoisted` when making
# it wrote a line.
struct Term
  gen: Gen
  text: String
  atom: Bool
  hoisted: Bool
end

# A call or operator before it is bound: `halts` when it returns `M`.
struct Parts
  gen: Gen
  text: String
  atom: Bool
  halts: Bool
  hoisted: Bool
end

# The lines of one function so far, at `indent`, with the next fresh name, the names it must not take, and the
# prelude modules it uses. `terminal` is true when the last line leaves the function.
struct Gen
  lines: List[String]
  indent: Int
  next: Int
  taken: Set[String]
  modules: Set[String]
  terminal: Bool
  namespace: String
end

struct Arguments
  gen: Gen
  texts: List[String]
  hoisted: Bool
end

struct Function
  text: String
  modules: Set[String]
end

# A builtin of the prelude: its Lean name, whether it returns `M`, and its module.
struct Builtin
  lean: String
  halts: Bool
  module: String
end

def header(job: Job) -> String
  "-- Generated by translator/main.agc from #{job.source}. Do not edit: CI checks it with --check.\n"
end

def doc(job: Job) -> String
  (
    "/-!\n# `#{job.source}`, translated\n\nGenerated by `translator/main.agc` from `#{job.source}` of the pinned " +
    "agentica\n(`.github/workflows/ci.yml`), with the rules of `docs/translator.md`.\n-/\n\n"
  )
end

# The functions to write, callees first, each once; a cycle is refused.
def ordered(functions: Map[String, Analysis.Body], roots: List[String]) -> Result[List[String]]
  done: List[String] = []
  for root in roots
    done = try visit(functions, root, [], done)
  end
  ok(done)
end

def visit(
  functions: Map[String, Analysis.Body],
  name: String,
  path: List[String],
  done: List[String],
) -> Result[List[String]]
  return ok(done) if done.include?(name)
  return error("#{name}: recursion (#{path.push(name).join(" -> ")}) is a later step") if path.include?(name)
  return error("#{name}: no such function with a body") if !functions.key?(name)

  result = done
  for callee in calls(functions[name].body, functions)
    result = try visit(functions, callee, path.push(name), result)
  end
  ok(result.push(name))
end

# The functions of the file that `nodes` call, in order, each once.
def calls(nodes: List[Analysis.Node], functions: Map[String, Analysis.Body]) -> List[String]
  nodes.reduce([]) do |found: List[String], node|
    inner = calls(node.children, functions)
    own = choose(node.kind == "call" and functions.key?(node.target), [node.target], [])
    (found + own + inner).uniq
  end
end

def function_text(functions: Map[String, Analysis.Body], body: Analysis.Body, namespace: String) -> Result[Function]
  return error("#{body.name}: not pure (#{reasons(body)})") if !body.pure
  return error("#{body.name}: generic functions are a later step") if !body.generics.empty?

  params = try parameters(body)
  result = try lean_type(body.result, body.name)
  taken = Set.new(names(body) + functions.keys)
  start = Gen(lines: [], indent: 2, next: 1, taken: taken, modules: Set.new([]), terminal: false, namespace: namespace)

  gen = try block(functions, start, body.body, true)
  if !gen.terminal
    return error("#{body.name}: a path ends without a value") if !(result == "Unit")

    gen = emit(gen, "Pure.pure ()")
  end
  head = "def #{ident(body.linked)}#{params} : M #{wrap(result)} :="
  one = gen.lines.size == 1 and simple?(gen.lines[0])
  text = choose(one, "#{head}\n#{gen.lines.join("\n")}", "#{head} do\n#{gen.lines.join("\n")}")
  ok(Function(text: text, modules: gen.modules))
end

def reasons(body: Analysis.Body) -> String = body.impure.map { |r| "#{r.effect} in #{r.call}" }.join(", ")

def simple?(line: String) -> Bool
  text = line.strip
  !(
    text.start_with?("return ") or
    text.start_with?("let ") or
    text.start_with?("match ") or
    text.start_with?("if ") or
    text.start_with?("|")
  )
end

# The parameters, with the names of a run of one type together: ` (offset n : AInt)`.
def parameters(body: Analysis.Body) -> Result[String]
  groups: List[String] = []
  names: List[String] = []
  current = ""
  for p in body.params
    return error("#{body.name}: a default for #{p.name} is a later step") if !p.default.empty?

    t = try lean_type(p.type, body.name)
    if t != current and !names.empty?
      groups = groups.push(" (#{names.join(" ")} : #{current})")
      names = []
    end
    names = names.push(ident(p.name))
    current = t
  end
  if !names.empty?
    groups = groups.push(" (#{names.join(" ")} : #{current})")
  end
  ok(groups.join(""))
end

def lean_type(shape: Analysis.TypeShape, where: String) -> Result[String]
  return error("#{where}: the type #{shape.name} is a later step") if !(shape.kind == "builtin")

  case shape.name
    "Int" -> ok("AInt")
    "Bool" -> ok("Bool")
    "String" -> ok("String")
    "Bytes" -> ok("Bytes")
    "Void" -> ok("Unit")
    "Result" -> ok("Result #{wrap(try lean_type(shape.args[0], where))}")
    "Optional" -> ok("Option #{wrap(try lean_type(shape.args[0], where))}")
    "List" -> ok("List #{wrap(try lean_type(shape.args[0], where))}")
    _ -> error("#{where}: the type #{shape.name} is a later step")
  end
end

def wrap(text: String) -> String = choose(text.include?(" "), "(#{text})", text)

def arg(term: Term) -> String = choose(term.atom, term.text, "(#{term.text})")

# Every name of the function: its parameters, locals and pattern bindings, which a fresh name must not take.
def names(body: Analysis.Body) -> List[String] = body.params.map { |p| p.name } + node_names(body.body)

def node_names(nodes: List[Analysis.Node]) -> List[String]
  nodes.reduce([]) do |found: List[String], node|
    own = choose(node.kind == "let" or node.kind == "bind", [node.text], [])
    found + own + node_names(node.children)
  end
end

def ident(name: String) -> String = choose(KEYWORDS.include?(name), "«#{name}»", name)

def emit(gen: Gen, line: String) -> Gen = gen.with(lines: gen.lines.push(" " * gen.indent + line), terminal: false)

def fresh(gen: Gen) -> Term
  name = "t#{gen.next}"
  next_gen = gen.with(next: gen.next + 1)
  return fresh(next_gen) if gen.taken.include?(name)

  Term(gen: next_gen.with(taken: next_gen.taken.add(name)), text: name, atom: true, hoisted: true)
end

def refuse(node: Analysis.Node, what: String) -> String
  "line #{node.range.start.line}:#{node.range.start.column}: #{what} is a later step"
end

# The statements `nodes` at the generator's indent. `last` is true for the end of the function, where a call that
# returns `M` of the result is written as it is.
def block(functions: Map[String, Analysis.Body], start: Gen, nodes: List[Analysis.Node], last: Bool) -> Result[Gen]
  gen = start
  count = nodes.size
  for i in 0...count
    gen = try statement(functions, gen, nodes[i], last and i == count - 1)
  end
  ok(gen)
end

def statement(functions: Map[String, Analysis.Body], gen: Gen, node: Analysis.Node, last: Bool) -> Result[Gen]
  case node.kind
    "let" -> bind(functions, gen, node, ident(node.text))
    "discard" -> bind(functions, gen, node, "_")
    "try" -> try_statement(functions, gen, node)
    "return" -> return_statement(functions, gen, node, last)
    "if" -> if_statement(functions, gen, node.children)
    "call", "op", "neg" ->
      parts = try value(functions, gen, node)
      return error(refuse(node, "a pure value as a statement")) if !parts.halts

      ok(emit(parts.gen, parts.text))
    _ -> error(refuse(node, "the statement #{node.kind}"))
  end
end

def bind(functions: Map[String, Analysis.Body], gen: Gen, node: Analysis.Node, name: String) -> Result[Gen]
  return error(refuse(node, "a new value for #{node.text}")) if node.kind == "let" and !node.new

  child = node.children[0]
  return match_try(functions, gen, child, "| .ok #{name} =>", true) if child.kind == "try"

  parts = try value(functions, gen, child)
  arrow = choose(parts.halts, "←", ":=")
  ok(emit(parts.gen, "let #{name} #{arrow} #{parts.text}"))
end

def try_statement(functions: Map[String, Analysis.Body], gen: Gen, node: Analysis.Node) -> Result[Gen]
  match_try(functions, gen, node, "| .ok _ => Pure.pure ()", false)
end

# `try e`: a `match` whose `error` arm returns the error. With `nested`, the rest of the block goes in the `ok` arm,
# one level in.
def match_try(
  functions: Map[String, Analysis.Body],
  gen: Gen,
  node: Analysis.Node,
  ok_line: String,
  nested: Bool,
) -> Result[Gen]
  parts = try value(functions, gen, node.children[0])
  head = choose(parts.halts, "match ← #{parts.text} with", "match #{parts.text} with")
  lines = (
    parts.gen
    |> emit(head)
    |> emit("| .error e => return .error e")
    |> emit(ok_line)
  )

  ok(lines.with(indent: choose(nested, gen.indent + 2, gen.indent)))
end

def return_statement(functions: Map[String, Analysis.Body], gen: Gen, node: Analysis.Node, last: Bool) -> Result[Gen]
  return ok(emit(gen, "return ()").with(terminal: true)) if node.children.empty?

  parts = try value(functions, gen, node.children[0])
  if parts.halts
    return ok(emit(parts.gen, parts.text).with(terminal: true)) if last

    name = fresh(parts.gen)
    return ok(emit(emit(name.gen, "let #{name.text} ← #{parts.text}"), "return #{name.text}").with(terminal: true))
  end
  ok(emit(parts.gen, "return #{parts.text}").with(terminal: true))
end

# `if`, `elsif` and `else`: the condition of a branch is made before its `if`, an `elsif` inside the `else`.
def if_statement(functions: Map[String, Analysis.Body], gen: Gen, branches: List[Analysis.Node]) -> Result[Gen]
  first = branches[0]
  return block(functions, gen, first.children, false) if first.kind == "block"

  condition = try expr(functions, gen, first.children[0], true)
  at = condition.gen
  inner = at.with(lines: [], indent: at.indent + 2)
  then_gen = try closed(try block(functions, inner, first.children[1].children, false))
  lines = emit(at, "if #{condition.text} then").lines + then_gen.lines
  rest = branches.drop(1)
  if rest.empty?
    return ok(
      at.with(lines: lines, next: then_gen.next, taken: then_gen.taken, modules: then_gen.modules, terminal: false),
    )
  end
  else_start = then_gen.with(lines: [], indent: at.indent + 2)
  else_gen = try closed(try if_statement(functions, else_start, rest))
  all = emit(at.with(lines: lines), "else").lines + else_gen.lines
  ok(
    at.with(
      lines: all,
      next: else_gen.next,
      taken: else_gen.taken,
      modules: else_gen.modules,
      terminal: then_gen.terminal and else_gen.terminal,
    ),
  )
end

# A branch that does not leave the function ends with `pure ()`, so it is a statement of the block around it.
def closed(gen: Gen) -> Result[Gen]
  return ok(gen) if gen.terminal

  ok(emit(gen, "Pure.pure ()"))
end

# A call or an operator, not yet bound, or any other expression as a term.
def value(functions: Map[String, Analysis.Body], gen: Gen, node: Analysis.Node) -> Result[Parts]
  return parts(functions, gen, node, true) if node.kind == "call" or node.kind == "op" or node.kind == "neg"

  term = try expr(functions, gen, node, true)
  ok(Parts(gen: term.gen, text: term.text, atom: term.atom, halts: false, hoisted: term.hoisted))
end

# An expression as a term. A call that returns `M` is bound to a fresh name first (`let t ← ...`), and so is a call
# below the top of a statement whose arguments needed lines of their own (`let t := ...`).
def expr(functions: Map[String, Analysis.Body], gen: Gen, node: Analysis.Node, top: Bool) -> Result[Term]
  case node.kind
    "int" ->
      ok(
        Term(
          gen: gen.with(modules: gen.modules.add("Agentica.Prelude.Int")),
          text: int_literal(node.text),
          atom: true,
          hoisted: false,
        ),
      )
    "string" -> ok(Term(gen: gen, text: lean_string(node.text), atom: true, hoisted: false))
    "bool" -> ok(Term(gen: gen, text: node.text, atom: true, hoisted: false))
    "local" -> ok(Term(gen: gen, text: ident(node.text), atom: true, hoisted: false))
    "call", "op", "neg" ->
      p = try parts(functions, gen, node, top)
      if p.halts
        name = fresh(p.gen)
        return ok(name.with(gen: emit(name.gen, "let #{name.text} ← #{p.text}")))
      end
      if p.hoisted and !top
        name = fresh(p.gen)
        return ok(name.with(gen: emit(name.gen, "let #{name.text} := #{p.text}")))
      end
      ok(Term(gen: p.gen, text: p.text, atom: p.atom, hoisted: p.hoisted))
    "or" -> short(functions, gen, node, true)
    "and" -> short(functions, gen, node, false)
    "not" ->
      t = try expr(functions, gen, node.children[0], false)
      ok(Term(gen: t.gen, text: "(!#{arg(t)})", atom: true, hoisted: t.hoisted))
    "interpolation" -> interpolation(functions, gen, node)
    "list" ->
      a = try arguments(functions, gen, node, [])
      ok(Term(gen: a.gen, text: "[#{a.texts.join(", ")}]", atom: true, hoisted: a.hoisted))
    "try" ->
      name = fresh(gen)
      g = try match_try(functions, name.gen, node, "| .ok #{name.text} =>", true)
      ok(name.with(gen: g))
    _ -> error(refuse(node, "the expression #{node.kind}"))
  end
end

# `a or b` is `if a then true else b`, and `a and b` is `if a then b else false`: `b` runs only when the VM runs it.
# When `b` needs lines, they go in a `do` of their own.
def short(functions: Map[String, Analysis.Body], gen: Gen, node: Analysis.Node, is_or: Bool) -> Result[Term]
  left = try expr(functions, gen, node.children[0], true)
  inner = left.gen.with(lines: [], indent: left.gen.indent + 2)
  right = try expr(functions, inner, node.children[1], true)
  return error(refuse(node, "try on the right of #{node.kind}")) if right.gen.indent != inner.indent
  after = left.gen.with(next: right.gen.next, taken: right.gen.taken, modules: right.gen.modules)
  if right.gen.lines.empty?
    text = choose(
      is_or,
      "if #{left.text} then true else #{right.text}",
      "if #{left.text} then #{right.text} else false",
    )

    return ok(Term(gen: after, text: "(#{text})", atom: true, hoisted: left.hoisted))
  end
  name = fresh(after)
  body = right.gen.lines.push(" " * (gen.indent + 2) + "Pure.pure #{arg(right)}")
  head = choose(
    is_or,
    "let #{name.text} ← if #{left.text} then Pure.pure true else do",
    "let #{name.text} ← if #{left.text} then do",
  )

  g = emit(name.gen, head)
  lines = g.lines + body
  if !is_or
    lines = lines.push(" " * gen.indent + "else Pure.pure false")
  end
  ok(name.with(gen: g.with(lines: lines)))
end

def interpolation(functions: Map[String, Analysis.Body], gen: Gen, node: Analysis.Node) -> Result[Term]
  g = gen
  pieces: List[String] = []
  hoisted = false
  for child in node.children
    t = try expr(functions, g, child, false)
    g = t.gen
    hoisted = hoisted or t.hoisted
    if child.type.name == "Int"
      g = g.with(modules: g.modules.add("Agentica.Prelude.String.FromInt"))
      pieces = pieces.push("Agentica.String.from_int #{arg(t)}")
    elsif child.type.name == "String"
      pieces = pieces.push(t.text)
    else
      return error(refuse(child, "an interpolation of #{child.type.name}"))
    end
  end
  return ok(Term(gen: g, text: "\"\"", atom: true, hoisted: false)) if pieces.empty?

  ok(Term(gen: g, text: pieces.join(" ++ "), atom: pieces.size == 1 and !pieces[0].include?(" "), hoisted: hoisted))
end

# A call or an operator: its target, and its arguments as terms.
def parts(functions: Map[String, Analysis.Body], gen: Gen, node: Analysis.Node, top: Bool) -> Result[Parts]
  return operator(functions, gen, node) if node.kind == "neg" or node.kind == "op"
  case node.target
    "ok" -> result_call(functions, gen, node, top)
    "error" -> error_call(functions, gen, node, top)
    _ ->
      if functions.key?(node.target)
        a = try arguments(functions, gen, node, functions[node.target].params.map { |p| p.name })
        text = (["#{gen.namespace}.#{ident(node.target)}"] + a.texts).join(" ")
        return ok(Parts(gen: a.gen, text: text, atom: a.texts.empty?, halts: true, hoisted: a.hoisted))
      end
      return error(refuse(node, "the builtin #{node.target}")) if !BUILTINS.key?(node.target)

      builtin_call(functions, gen, node, BUILTINS[node.target])
  end
end

# A unary minus or a binary operator, by the type of its first operand.
def operator(functions: Map[String, Analysis.Body], gen: Gen, node: Analysis.Node) -> Result[Parts]
  operand = node.children[0].type.name
  if node.kind == "neg"
    return error(refuse(node, "unary minus on #{operand}")) if operand != "Int"

    return builtin_call(functions, gen, node, NEG)
  end
  if node.kind == "op"
    return builtin_call(functions, gen, node, BYTES_PLUS) if operand == "Bytes" and node.text == "+"

    known = operand == "Int" and OPERATORS.key?(node.text)
    return error(refuse(node, "the operator #{node.text} on #{operand}")) if !known

    return builtin_call(functions, gen, node, OPERATORS[node.text])
  end
  error(refuse(node, "the expression #{node.kind}"))
end

# The arguments in the order the VM runs them, which is the order of `children`; a `named` node (its text the
# parameter name) goes to the place of its parameter in `params`.
def arguments(
  functions: Map[String, Analysis.Body],
  gen: Gen,
  node: Analysis.Node,
  params: List[String],
) -> Result[Arguments]
  g = gen
  texts: Map[Int, String] = {}
  hoisted = false
  for i in 0...node.children.size
    child = node.children[i]
    place = i
    value = child
    if child.kind == "named"
      found = (0...params.size).to_a.select { |k| params[k] == child.text }
      return error(refuse(child, "the named argument #{child.text}")) if found.empty?

      place = found[0]
      value = child.children[0]
    end
    t = try expr(functions, g, value, false)
    g = t.gen
    texts = texts.put(place, arg(t))
    hoisted = hoisted or t.hoisted
  end
  ok(Arguments(gen: g, texts: (0...texts.size).map { |i| texts[i] }, hoisted: hoisted))
end

def builtin_call(
  functions: Map[String, Analysis.Body],
  gen: Gen,
  node: Analysis.Node,
  builtin: Builtin,
) -> Result[Parts]
  a = try arguments(functions, gen, node, [])
  g = a.gen.with(modules: a.gen.modules.add(builtin.module))
  ok(Parts(gen: g, text: ([builtin.lean] + a.texts).join(" "), atom: false, halts: builtin.halts, hoisted: a.hoisted))
end

# `ok(x)` and `ok()`: the argument stays at the top of the statement.
def result_call(functions: Map[String, Analysis.Body], gen: Gen, node: Analysis.Node, top: Bool) -> Result[Parts]
  return ok(Parts(gen: gen, text: ".ok ()", atom: false, halts: false, hoisted: false)) if node.children.empty?

  t = try expr(functions, gen, node.children[0], top)
  ok(Parts(gen: t.gen, text: ".ok #{arg(t)}", atom: false, halts: false, hoisted: t.hoisted))
end

# `error(message)` and `error(message, kind: k)`: the `Error` record, its kind `"error"` by default.
def error_call(functions: Map[String, Analysis.Body], gen: Gen, node: Analysis.Node, top: Bool) -> Result[Parts]
  return error(refuse(node, "error(e) with an Error")) if node.children[0].type.name != "String"

  kind_node = node.children.size == 2 and node.children[1].kind == "named" and node.children[1].text == "kind"
  only_kind = node.children.size == 1 or (kind_node and node.children[1].children[0].type.name == "String")
  return error(refuse(node, "error(...) with code, details or cause")) if !only_kind

  message = try expr(functions, gen, node.children[0], top)
  g = message.gen
  kind = ""
  hoisted = message.hoisted
  if node.children.size == 2
    k = try expr(functions, g, node.children[1].children[0], top)
    g = k.gen
    kind = "kind := #{k.text}, "
    hoisted = hoisted or k.hoisted
  end
  ok(Parts(gen: g, text: ".error { #{kind}message := #{message.text} }", atom: false, halts: false, hoisted: hoisted))
end

def choose[T](condition: Bool, yes: T, no: T) -> T
  return yes if condition

  no
end

def int_literal(text: String) -> String
  return "(Agentica.AInt.ofInt (#{text}))" if text.start_with?("-")

  "(Agentica.AInt.ofInt #{text})"
end

def lean_string(text: String) -> String
  body = text.split("").map { |c| lean_char(c) }.join("")
  "\"#{body}\""
end

def lean_char(c: String) -> String
  case c
    "\\" -> "\\\\"
    "\"" -> "\\\""
    "\n" -> "\\n"
    "\t" -> "\\t"
    "\r" -> "\\r"
    _ -> choose(c.code < 32, format("\\x%02x", c.code), c)
  end
end

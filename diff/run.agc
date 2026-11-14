# Runs the cases of `lake exe diffcases` on agentica (see Diff/Main.lean).
#
# Usage: agentica diff/run.agc CASES.tsv START
#
# Prints `id<TAB>result` for each case from id START on, in the format of the
# expected results. A case that halts ends the program with its diagnostic;
# scripts/difftest.py records the code and starts again after it.
#
# The harness reads and checks every argument before it calls a builtin, and
# never halts itself: a bad case prints `harness ...`. Each builtin call is in
# its own `call_` function, so a halt is a result only when its stack reaches
# one of them (scripts/difftest.py checks).
import Binary from "std/binary"

def call_add(a: Int, b: Int) -> String
  return "int #{a + b}"
end

def call_sub(a: Int, b: Int) -> String
  return "int #{a - b}"
end

def call_bit_and(a: Int, b: Int) -> String
  return "int #{a.bit_and(b)}"
end

def call_bit_or(a: Int, b: Int) -> String
  return "int #{a.bit_or(b)}"
end

def call_bit_xor(a: Int, b: Int) -> String
  return "int #{a.bit_xor(b)}"
end

def call_bit_not(a: Int) -> String
  return "int #{a.bit_not}"
end

def call_from_int(a: Int) -> String
  return "text #{a.to_s}"
end

def call_shift_left(a: Int, b: Int) -> String
  return "int #{a.shift_left(b)}"
end

def call_shift_right(a: Int, b: Int) -> String
  return "int #{a.shift_right(b)}"
end

def call_shift_right_unsigned(a: Int, b: Int) -> String
  return "int #{a.shift_right_unsigned(b)}"
end

def call_eq(a: Int, b: Int) -> String
  return "bool #{a == b}"
end

def call_ne(a: Int, b: Int) -> String
  return "bool #{a != b}"
end

def call_lt(a: Int, b: Int) -> String
  return "bool #{a < b}"
end

def call_le(a: Int, b: Int) -> String
  return "bool #{a <= b}"
end

def call_gt(a: Int, b: Int) -> String
  return "bool #{a > b}"
end

def call_ge(a: Int, b: Int) -> String
  return "bool #{a >= b}"
end

def call_length(data: Bytes) -> String
  return "int #{data.size}"
end

def call_at(data: Bytes, i: Int) -> String
  return "int #{data[i]}"
end

def call_read_u16_le(data: Bytes, offset: Int) -> String
  return result_text(Binary.read_u16_le(data, offset))
end

def call_read_u16_be(data: Bytes, offset: Int) -> String
  return result_text(Binary.read_u16_be(data, offset))
end

def call_read_u32_le(data: Bytes, offset: Int) -> String
  return result_text(Binary.read_u32_le(data, offset))
end

def call_read_u64_le(data: Bytes, offset: Int) -> String
  return result_text(Binary.read_u64_le(data, offset))
end

def call_read_i64_le(data: Bytes, offset: Int) -> String
  return result_text(Binary.read_i64_le(data, offset))
end

def call_read_i16_le(data: Bytes, offset: Int) -> String
  return result_text(Binary.read_i16_le(data, offset))
end

def call_read_i32_le(data: Bytes, offset: Int) -> String
  return result_text(Binary.read_i32_le(data, offset))
end

def call_read_u8(data: Bytes, offset: Int) -> String
  return result_text(Binary.read_u8(data, offset))
end

def call_read_i8(data: Bytes, offset: Int) -> String
  return result_text(Binary.read_i8(data, offset))
end

def call_read_u32_be(data: Bytes, offset: Int) -> String
  return result_text(Binary.read_u32_be(data, offset))
end

def call_read_u64_be(data: Bytes, offset: Int) -> String
  return result_text(Binary.read_u64_be(data, offset))
end

def call_read_i16_be(data: Bytes, offset: Int) -> String
  return result_text(Binary.read_i16_be(data, offset))
end

def call_read_i32_be(data: Bytes, offset: Int) -> String
  return result_text(Binary.read_i32_be(data, offset))
end

def call_read_i64_be(data: Bytes, offset: Int) -> String
  return result_text(Binary.read_i64_be(data, offset))
end

def call_read_frame_length(data: Bytes, offset: Int, max: Int) -> String
  return result_text(Binary.read_frame_length(data, offset, max))
end

# The text of a reader's Result. It never halts.
def result_text(found: Result[Int]) -> String
  case found
    ok(n) -> "ok #{n}"
    error(e) -> "error #{e.kind} #{e.message}"
  end
end

# The number of arguments of each function, the first one a Bytes for the
# readers, `length` and `at`; -1 for a name the harness does not know.
def arity(name: String) -> Int
  if name == "bit_not" or name == "from_int" or name == "length"
    return 1
  end
  two = ["add", "sub", "bit_and", "bit_or", "bit_xor", "shift_left", "shift_right",
    "shift_right_unsigned", "eq", "ne", "lt", "le", "gt", "ge", "at", "read_u16_le", "read_u16_be",
    "read_u32_le", "read_u64_le", "read_i64_le", "read_i16_le", "read_i32_le", "read_u8", "read_i8",
    "read_u32_be", "read_u64_be", "read_i16_be", "read_i32_be", "read_i64_be"]
  if two.any? do |x| x == name end
    return 2
  end
  if name == "read_frame_length"
    return 3
  end
  return -1
end

def takes_bytes(name: String) -> Bool
  return name == "length" or name == "at" or name.start_with?("read_")
end

# The bytes of a comma list (`-` for none), or an error.
def parse_bytes(text: String) -> Result[Bytes]
  if text == "-"
    return Bytes.from_list([])
  end
  items: List[Int] = []
  for part in text.split(",")
    items = items.push(try part.to_i)
  end
  return Bytes.from_list(items)
end

# Checks and parses a case, then calls its builtin. Only the `call_` functions
# may halt.
def run_case(name: String, args: List[String]) -> String
  if arity(name) < 0 or args.size != arity(name)
    return "harness bad case: #{name} with #{args.size} arguments"
  end
  ints: List[Int] = []
  first = 0
  data = Bytes.from_list([]).unwrap!
  if takes_bytes(name)
    parsed = parse_bytes(args[0])
    if not parsed.ok?
      return "harness bad bytes: #{args[0]}"
    end
    data = parsed.unwrap!
    first = 1
  end
  for k in first...args.size
    value = args[k].to_i
    if not value.ok?
      return "harness bad Int: #{args[k]}"
    end
    ints = ints.push(value.unwrap!)
  end
  if name == "length"
    return call_length(data)
  elsif name == "at"
    return call_at(data, ints[0])
  elsif name == "read_u16_le"
    return call_read_u16_le(data, ints[0])
  elsif name == "read_u16_be"
    return call_read_u16_be(data, ints[0])
  elsif name == "read_u32_le"
    return call_read_u32_le(data, ints[0])
  elsif name == "read_u64_le"
    return call_read_u64_le(data, ints[0])
  elsif name == "read_i64_le"
    return call_read_i64_le(data, ints[0])
  elsif name == "read_i16_le"
    return call_read_i16_le(data, ints[0])
  elsif name == "read_i32_le"
    return call_read_i32_le(data, ints[0])
  elsif name == "read_u8"
    return call_read_u8(data, ints[0])
  elsif name == "read_i8"
    return call_read_i8(data, ints[0])
  elsif name == "read_u32_be"
    return call_read_u32_be(data, ints[0])
  elsif name == "read_u64_be"
    return call_read_u64_be(data, ints[0])
  elsif name == "read_i16_be"
    return call_read_i16_be(data, ints[0])
  elsif name == "read_i32_be"
    return call_read_i32_be(data, ints[0])
  elsif name == "read_i64_be"
    return call_read_i64_be(data, ints[0])
  elsif name == "read_frame_length"
    return call_read_frame_length(data, ints[0], ints[1])
  elsif name == "bit_not"
    return call_bit_not(ints[0])
  elsif name == "from_int"
    return call_from_int(ints[0])
  end
  a = ints[0]
  b = ints[1]
  if name == "add"
    return call_add(a, b)
  elsif name == "sub"
    return call_sub(a, b)
  elsif name == "bit_and"
    return call_bit_and(a, b)
  elsif name == "bit_or"
    return call_bit_or(a, b)
  elsif name == "bit_xor"
    return call_bit_xor(a, b)
  elsif name == "shift_left"
    return call_shift_left(a, b)
  elsif name == "shift_right"
    return call_shift_right(a, b)
  elsif name == "shift_right_unsigned"
    return call_shift_right_unsigned(a, b)
  elsif name == "eq"
    return call_eq(a, b)
  elsif name == "ne"
    return call_ne(a, b)
  elsif name == "lt"
    return call_lt(a, b)
  elsif name == "le"
    return call_le(a, b)
  elsif name == "gt"
    return call_gt(a, b)
  end
  return call_ge(a, b)
end

def main() -> Void
  args = System.args()
  if args.size != 2
    puts("harness usage: run.agc CASES.tsv START")
    return
  end
  text = File.read_text(args[0])
  start = args[1].to_i
  if not text.ok? or not start.ok?
    puts("harness cannot read #{args[0]} or start #{args[1]}")
    return
  end
  for line in text.unwrap!.split("\n")
    fields = line.split("\t")
    if line == "" or fields.size != 4
      if line != ""
        puts("harness bad line: #{line}")
      end
      next
    end
    id = fields[0].to_i
    if not id.ok?
      puts("harness bad id: #{line}")
      next
    end
    if id.unwrap! >= start.unwrap!
      case_args: List[String] = []
      if fields[2] != ""
        case_args = fields[2].split(" ")
      end
      found = run_case(fields[1], case_args)
      puts("#{id.unwrap!}\t#{found}")
      IO.flush()
    end
  end
end

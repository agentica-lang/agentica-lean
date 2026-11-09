# Runs the cases of `lake exe diffcases` on agentica (see Diff/Main.lean).
#
# Usage: agentica diff/run.agc CASES.tsv START
#
# Prints `id<TAB>result` for each case from id START on, in the format of the
# expected results. A case that halts ends the program with its diagnostic;
# scripts/difftest.py records the code and starts again after it.
import Binary from "std/binary"

def int_arg(text: String) -> Int
  return text.to_i!
end

def bytes_arg(text: String) -> Bytes
  if text == "-"
    return Bytes.from_list([]).unwrap!
  end
  items = text.split(",").map do |part|
    part.to_i!
  end
  return Bytes.from_list(items).unwrap!
end

def int_result(value: Int) -> String
  return "int #{value}"
end

def bool_result(value: Bool) -> String
  return "bool #{value}"
end

def result_text(found: Result[Int]) -> String
  if found.ok?
    return "ok #{found.unwrap!}"
  end
  return "error #{found.message}"
end

def run_bytes(name: String, args: List[String]) -> String
  data = bytes_arg(args[0])
  if name == "length"
    return int_result(data.size)
  elsif name == "at"
    return int_result(data[int_arg(args[1])])
  end
  return result_text(Binary.read_u16_le(data, int_arg(args[1])))
end

def run_case(name: String, args: List[String]) -> String
  if name == "length" or name == "at" or name == "read_u16_le"
    return run_bytes(name, args)
  end
  a = int_arg(args[0])
  if name == "bit_not"
    return int_result(a.bit_not)
  elsif name == "from_int"
    return "text #{a.to_s}"
  end
  b = int_arg(args[1])
  if name == "add"
    return int_result(a + b)
  elsif name == "sub"
    return int_result(a - b)
  elsif name == "bit_and"
    return int_result(a.bit_and(b))
  elsif name == "bit_or"
    return int_result(a.bit_or(b))
  elsif name == "bit_xor"
    return int_result(a.bit_xor(b))
  elsif name == "shift_left"
    return int_result(a.shift_left(b))
  elsif name == "shift_right"
    return int_result(a.shift_right(b))
  elsif name == "shift_right_unsigned"
    return int_result(a.shift_right_unsigned(b))
  elsif name == "eq"
    return bool_result(a == b)
  elsif name == "ne"
    return bool_result(a != b)
  elsif name == "lt"
    return bool_result(a < b)
  elsif name == "le"
    return bool_result(a <= b)
  elsif name == "gt"
    return bool_result(a > b)
  elsif name == "ge"
    return bool_result(a >= b)
  end
  return "unknown function #{name}"
end

def main() -> Void
  args = System.args()
  text = File.read_text(args[0]).unwrap!
  start = args[1].to_i!
  for line in text.split("\n")
    if line == ""
      next
    end
    fields = line.split("\t")
    id = fields[0].to_i!
    if id >= start
      found = run_case(fields[1], fields[2].split(" "))
      puts("#{id}\t#{found}")
      IO.flush()
    end
  end
end

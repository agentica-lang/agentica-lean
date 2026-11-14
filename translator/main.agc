## Writes the Lean translations of `JOBS` (run from the root of the repository): `agentica translator/main.agc`.
## `--check` translates again in memory and exits 1 with the list of files that differ.

import Analysis from "std/analysis"
import Lean from "lean"

JOBS = [
  Lean.Job(
    source: "std/binary",
    roots: [
      "read_u8", "read_i8", "read_u16_be", "read_u16_le", "read_i16_be", "read_i16_le", "read_u32_be", "read_u32_le",
      "read_i32_be", "read_i32_le", "read_u64_be", "read_u64_le", "read_i64_be", "read_i64_le", "read_frame_length",
    ],
    path: "Agentica/Std/Binary.lean",
    namespace: "Agentica.Std.Binary",
  ),
]

def main() -> Void
  check = System.args().include?("--check")
  session = Analysis.open(Analysis.workspace())
  failed = false
  for job in JOBS
    case run(session, job, check)
      ok(_) -> nil
      error(e) ->
        IO.warn("translator: #{job.path}: #{e.message}")
        failed = true
    end
  end
  if failed
    System.exit(1)
  end
end

private

def run(session: Analysis.Session, job: Lean.Job, check: Bool) -> Result[Void]
  found = try Analysis.bodies(session, job.source)
  text = try Lean.translate(job, found)
  if check
    current = File.read_text(job.path).unwrap_or("")
    return error("stale: run agentica translator/main.agc") if current != text

    return ok()
  end
  File.write_text(job.path, text)
end

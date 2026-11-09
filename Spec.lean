-- The imports of every module under Spec/ go here, at the top of the file:
-- an import below the module doc would not parse.

/-!
# Agentica builtin specifications

The root of the `Spec` library. Each builtin gets one module under `Spec/`,
named after its type and method (`Spec/Int/ShiftRightUnsigned.lean` for
`Int.shift_right_unsigned`), and this file imports every one of them.
-/

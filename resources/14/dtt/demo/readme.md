# Introduction to Dependent Type Theory

There are two demos - one for Agda, one for Lean. The development
environment may be set up by entering a Nix shell with `nix develop`.

If you don't have Nix installed, then tough luck getting it to work.

## Agda

To look through the example, open the file `Agda/demo.agda` in you
editor (Emacs), and press `C-c C-l` to load it. Then try
`C-c C-n do-stuff` to print the normalized value of a function.

To compile the program, run `agda --compile demo.agda`. It should
produce a `demo` binary in the directory, which you may run as a
regular program.

## Lean

Again, open the file `Lean/Main.lean` in your editor (Emacs).
Hover over the `#eval` lines to get the output of the function calls.
Hover over the `#check Nat.rec` line to get the type of the "magical"
induction principle for natural numbers.

To compile the program, run `lake build` in the `Lean/` directory. The
binary is located in `.lake/build/bin/exe`. Alternatively you can run
it with `lake exe exe`.

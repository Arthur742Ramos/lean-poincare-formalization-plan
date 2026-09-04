/-!
# Contracted second Bianchi identity

The package root is a lightweight build target.  The proved tensor-level
identity is exposed by `Solution.lean`, while `Challenge.lean` is available as
a separate library for Comparator replay.  Keeping the root target independent
avoids a module-name collision with the parent path dependency, which also has
its own generic `Solution` library.
-/

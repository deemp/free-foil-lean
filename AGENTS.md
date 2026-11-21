# Repository Guidelines

This workspace currently has no checked-out source or readable Git history. The Lean and Lake guidance below is provisional until the project files are available.

## Project Structure

Start with the root README and `lakefile.lean` or `lakefile.toml`. The Lake configuration identifies library and executable targets and any custom source directories. Follow the existing module layout for new `.lean` files and keep regression examples with the project's existing checks. Use `git ls-files '*.lean'` to list tracked Lean files once the checkout is available.

## Build and Development

For a Lake checkout, run these commands from the package root with the Lean version pinned in `lean-toolchain`.

- `lake build` builds the default targets and checks the Lean modules they include.
- `lake lean path/to/Module.lean` builds a file's imports and checks the file.
- `lake test` and `lake lint` run the corresponding drivers when configured.

See the [Lake reference](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/) for command details.

## Style and Testing

Match nearby modules for indentation, naming, imports, and proof layout. For a proof regression, use a small Lean `example` that states the property being checked. For an executable regression, follow the project's test driver and existing test names. Run the affected check and the default build before opening a pull request.

## Commits and Pull Requests

Review recent subjects with `git log -12 --oneline` once history is available. Follow the [commit skill](.agents/skills/commit/SKILL.md) for every commit message. In the pull request, explain what changed and why, list the checks you ran, and link the relevant issue when one exists.

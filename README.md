# Higher Category Theory

Mathematical documentation exploring higher categorical structures and their applications.

## Documents

The repository contains two primary documents:
- **HCT Primer** (153KB): A systematic introduction to higher category theory foundations
- **HCT Working** (154KB): Applications and connections to concrete examples

View the formatted versions at the [index portal](https://j0pari.github.io/Higher-Category-Theory/).

## Build System

A JavaScript build system that converts source text files into HTML, PDF, and Markdown formats.

### Current Implementation

```bash
npm install
node build.js           # Watch mode - rebuilds on file changes
node build.js --push    # Build and push to GitHub
node build.js --no-watch # Single build, then exit
```

**What it does:**
- Converts HCT_*.txt source files to multiple output formats
- Renders LaTeX mathematics (inline and display mode)
- Generates table of contents with section numbering
- Creates formatted PDFs using Puppeteer
- Produces an index.html with file sizes and metadata
- Watches for changes and rebuilds automatically
- Implements content-addressed caching to avoid redundant builds
- Manages parallel builds with a task scheduler

**Core mechanisms:**
- Lazy evaluation pattern for deferred computation
- Pull-based dependency graph for build orchestration
- Causal debugging system that traces operation chains
- Pipeline composition using functional transformations
- Resource coordination to prevent file conflicts
- Artifact barriers to ensure proper build sequencing

### Configuration Architecture

The system uses a comprehensive CONFIG object that defines all specifics, while the machinery remains abstract. This separation enables the same computational substrate to manifest as different systems entirely.

**CONFIG controls:**
- Time constants, scheduling priorities, and retry strategies
- File paths, formats, and encoding specifications
- Mathematical constants built from prime factorizations
- Morphisms that transform between computational states
- Actor types that perform different kinds of work
- Contracts and invariants the system must maintain

**Abstract machinery provides:**
- Universal computation patterns (lazy, pull-based, morphism application)
- Generic dependency resolution and task scheduling
- Structure-preserving transformations between representations
- Artifact synchronization and barrier coordination
- Resource management with linear safety guarantees

This architecture points toward a system where CONFIG fully specifies the computation topology while the code provides only the abstract categorical machinery - a complete separation of "what" from "how".

## License

MIT License - See LICENSE file for details.
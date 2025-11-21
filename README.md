# Higher Category Theory

Mathematical documentation exploring higher categorical structures and their applications.

## Documents

The repository contains two primary documents:
- **HCT Primer** (153KB): A systematic introduction to higher category theory foundations
- **HCT Working** (154KB): Applications and connections to concrete examples

View the formatted versions at the [index portal](https://j0pari.github.io/Higher-Category-Theory/output/).

## Build System

A JavaScript build system that converts source text files into HTML, PDF, and Markdown formats.

### Current Implementation

```bash
npm install
node scripts/builder.js           # Watch mode - rebuilds on file changes
node scripts/builder.js --push    # Build and push to GitHub
node scripts/builder.js --no-watch # Single build, then exit
```

**What it does:**
- Converts source text files to HTML, PDF, and Markdown
- Renders LaTeX mathematics using KaTeX
- Generates PDFs via Puppeteer with proper page breaks
- Creates an index with file metadata and cache-busting
- Watches for changes and rebuilds incrementally
- Provides socket-based debug interface (port 9999) for querying build state

**Implementation details:**
- Lazy evaluation: computation deferred until results are pulled
- Pull promises: async operations that only run when pulled
- Causal debugger: traces event chains with timestamps and memory snapshots
- Pipeline composition: HTML → PDF → Markdown transformations
- Task scheduler: manages concurrent builds with priority queuing
- Socket server: allows CLI queries of running build state via TCP

The build system uses a CONFIG object to specify all concrete details (file paths, time constants, priorities) while the code provides abstract computation patterns. The same lazy evaluation and pull-based machinery could orchestrate entirely different systems by changing only the CONFIG.

**Debug Interface:**

When running with `DEBUG=1`, a socket server starts on port 9999 allowing queries of the running build:

```bash
# Query recent events
echo '{"id":1,"query":"events.recent","args":[10]}' | nc localhost 9999

# Check build state
echo '{"id":2,"query":"build.cache","args":[]}' | nc localhost 9999

# Performance metrics
echo '{"id":3,"query":"perf.metrics","args":[]}' | nc localhost 9999
```

The debug interface provides event tracing, causal chains, performance profiling, and build state inspection. Responses use delta compression for large results and gzip compression for responses over 1KB.

## License

MIT License - See LICENSE file for details.
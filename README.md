# Higher Category Theory

Mathematical documentation exploring higher categorical structures and their applications.

## Documents

The repository contains two primary documents:
- **HCT Primer** (157KB): Systematic introduction to higher category theory foundations
- **HCT Working** (160KB): Applications and concrete examples

View the formatted versions at the [index portal](https://j0pari.github.io/Higher-Category-Theory/output/).

## Build System

A JavaScript build system that converts source text files into HTML, PDF, and Markdown formats.

### Current Implementation

```bash
node scripts/builder.js  # Builds documents and enters watch mode
```

**What it does:**
- Converts source text files to HTML, PDF, and Markdown
- Renders LaTeX mathematics using KaTeX
- Generates PDFs via Puppeteer
- Creates an index with file metadata
- Watches for changes and rebuilds

**Implementation:**
- Lazy evaluation: computation deferred until pulled
- Pull-based dependency graph
- Event tracing with timestamps
- Format pipeline: text → HTML → PDF → Markdown
- Categorically defined files and dependencies in CONFIG

## License

MIT License - See LICENSE file for details.
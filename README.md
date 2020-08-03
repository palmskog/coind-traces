# Coinductive Traces

[![CI][action-shield]][action-link]

[action-shield]: https://github.com/palmskog/coind-traces/workflows/CI/badge.svg?branch=master
[action-link]: https://github.com/palmskog/coind-traces/actions?query=workflow%3ACI




Development in Coq of possibly-infinite traces and properties
of such traces via coinduction and corecursion, useful
for capturing labeled transition systems.

## Meta

- Author(s):
  - Keiko Nakata
  - Tarmo Uustalu
  - Karl Palmskog
- License: [MIT License](LICENSE)
- Compatible Coq versions: 8.10 or later
- Additional dependencies: none
- Coq namespace: `CoindTraces`
- Related publication(s): none

## Building instructions

``` shell
git clone https://github.com/palmskog/coind-traces
cd coind-traces
make   # or make -j <number-of-cores-on-your-machine>
```

## Files

- `Traces.v`: definition and decomposition of possibly-infinite traces
- `TraceProperties.v`: core trace properties such as finiteness and infiniteness
- `TraceClassicalProperties.v`: trace properties that require classical logic

Many definitions and properties are adapted from the
[Coinductive Trace-Based Semantics for While][coind-sem-url]
by Nakata and Uustalu.

[coind-sem-url]: https://github.com/palmskog/coind-sem-while

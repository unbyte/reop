<h1 align="center">ReOp</h1>

<p align="center">
<img alt="npm" src="https://img.shields.io/npm/v/reop?style=flat-square">
<img alt="GitHub" src="https://img.shields.io/github/license/unbyte/reop?style=flat-square">
<img alt="Codecov" src="https://img.shields.io/codecov/c/github/unbyte/reop?style=flat-square">
<img alt="GitHub Workflow Status" src="https://img.shields.io/github/actions/workflow/status/unbyte/reop/ci.yaml?style=flat-square">
</p>

<p align="center">
A port of <b>Result</b> and <b>Option</b> from Rust with ergonomic optimization, for Javascript / Typescript.
</p>

<h2 align="center">Documentation</h2>

Basically you can fully use your familiar API from Rust, for each API and corresponding description, see [documentation](https://paka.dev/npm/reop@latest).

In addition to things from Rust, this library also provides the convenience 
of interoperation between sync and async code.

Consider we are looking for the entry path of a npm package,
and we don't care what error occurs:

```javascript
import { Result } from 'reop'
import { resolve } from 'node:path'
import { readJson, exists } from 'fs-extra'

// ↓ Option<string>
const entry = 
  await Result
    .fromAsync(() => readJson(resolve(pkgPath, './package.json'))) // any error will be caught in Result::Err
    .ok() // turn to AsyncOption
    .map((pkg) => resolve(pkgPath, pkg.main))
    .filter((entry) => exists(entry)) // an async filter

for (const path of entry.iter()) {
    // do magic
}
```

Or using `wrap` helpers:

```javascript
const readJsonResult = Result.wrapAsync(readJson)

// ↓ Option<string>
const entry = await readJsonResult(resolve(pkgPath, './package.json'))
    .ok()
    .map((pkg) => resolve(pkgPath, pkg.main))
    .filter((entry) => exists(entry))
```

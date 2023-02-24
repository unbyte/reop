<h1 align="center">ReOp</h1>

<p align="center">
<a href="https://www.npmjs.com/package/reop"><img alt="npm" src="https://img.shields.io/npm/v/reop?style=flat-square"></a>
<img alt="GitHub" src="https://img.shields.io/github/license/unbyte/reop?style=flat-square">
<img alt="Codecov" src="https://img.shields.io/codecov/c/github/unbyte/reop?style=flat-square">
<img alt="GitHub Workflow Status" src="https://img.shields.io/github/actions/workflow/status/unbyte/reop/ci.yaml?style=flat-square">
</p>

<p align="center">
The Result and Option for Javascript/Typescript.
</p>

<h2 align="center">Documentation</h2>

The library's API is similar to Rust's, 
but integrates with the asynchronous language of Javascript.

Here assumes you have already known the usage of `Result` and `Option` in Rust,
so [complicated API descriptions](https://paka.dev/npm/reop@latest) can be skipped,
and the uniqueness of this library can be obvious.

Consider we are looking for the entry path of a npm package,
and we don't care what error occurs:

```javascript
import { Result } from 'reop'
import { resolve } from 'node:path'
import { readJson, exists } from 'fs-extra'

const entry = await Option
    .fromAsync(() => readJson(resolve(pkgPath, './package.json'))) // errors are caught as Option::None
    .map((pkg) => resolve(pkgPath, pkg.main))
    .filter((entry) => exists(entry)) // an async filter
    .iter() // does the same as what Option::iter in Rust does

for (const path of entry) {
    // ...
}
```

Or using `wrap` helpers:

```javascript
const readJsonOptional = Option.wrapAsync(readJson) // like what promisify() does

const entry = await readJsonOptional(resolve(pkgPath, './package.json'))
    .map((pkg) => resolve(pkgPath, pkg.main))
    .filter((entry) => exists(entry))
    .iter()
```

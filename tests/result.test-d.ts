import { Result, AsyncResult } from '../src'
import { expectType } from './common'

expectType<Result<number, boolean>>(Result.Ok(0))
expectType<Result<number, string>>(Result.Ok(0))

expectType<Result<number, number>>(Result.Err(0))
expectType<Result<string, number>>(Result.Err(0))

declare let resultA: Result<string, number>
declare let resultB: Result<Promise<string>, number>
declare let resultC: Result<string | Promise<string>, number>

expectType<AsyncResult<string, number>>(resultA.async())
expectType<AsyncResult<string, number | boolean>>(resultA.async())

// TODO: force `F = Error` ?
expectType<AsyncResult<string, number>>(resultB.async())
expectType<AsyncResult<string, number | boolean>>(resultB.async())

expectType<AsyncResult<string, number>>(resultC.async())
expectType<AsyncResult<string, number | boolean>>(resultC.async())

// promise-like
expectType<PromiseLike<Result<string, unknown>>>(resultA.async())
expectType<PromiseLike<Result<string, unknown>>>(resultA.async().await())

declare const fnA: () => string
declare const fnB: () => Promise<string>
declare const fnC: (n: number) => string | Promise<string>

expectType<() => Result<string, unknown>>(Result.wrap(fnA))
expectType<() => Result<Promise<string>, unknown>>(Result.wrap(fnB))
expectType<(n: number) => Result<string | Promise<string>, number>>(
  Result.wrap<string | Promise<string>, number>(fnC),
)

expectType<() => AsyncResult<string, unknown>>(Result.wrapAsync(fnA))
expectType<() => AsyncResult<string, unknown>>(Result.wrapAsync(fnB))
expectType<(n: number) => AsyncResult<string, number | boolean>>(
  Result.wrapAsync<string, number, boolean>(fnC),
)

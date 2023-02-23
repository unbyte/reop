import { Option, AsyncOption } from '../src'
import { expectType } from './common'

expectType<Option<number>>(Option.Some(0))

// any type
expectType<Option<number>>(Option.None)
expectType<Option<string>>(Option.None)

expectType<AsyncOption<number>>(Option.Some(0).async())
// promise-like
expectType<PromiseLike<Option<number>>>(Option.Some(0).async())
expectType<PromiseLike<Option<number>>>(Option.Some(0).async().await())

declare const fnA: () => string
declare const fnB: () => Promise<string>
declare const fnC: (n: number) => string | Promise<string>

expectType<() => Option<string>>(Option.wrap(fnA))
expectType<() => Option<Promise<string>>>(Option.wrap(fnB))
expectType<(n: number) => Option<string | Promise<string>>>(Option.wrap(fnC))

expectType<() => AsyncOption<string>>(Option.wrapAsync(fnA))
expectType<() => AsyncOption<string>>(Option.wrapAsync(fnB))
expectType<(n: number) => AsyncOption<string>>(Option.wrapAsync(fnC))

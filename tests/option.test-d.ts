import { Option } from '../src'
import { expectType } from './common'

// promise
expectType<Promise<Option<number>>>(Option.wrap(async () => 1).promise())
expectType<Promise<Option<number>>>(Option.wrap(() => 1).promise())

declare let fnA: () => Promise<number> | number
expectType<Promise<Option<number>>>(Option.wrap(fnA).promise())
expectType<Promise<Option<number>>>(
  Option.wrap(fnA)
    .map(async (n) => 1 + (await n))
    .promise(),
)

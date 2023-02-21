import { Result } from '../src'
import { expectType } from './common'

// promise
expectType<Promise<Result<number, Error>>>(Result.wrap(async () => 1).promise())
expectType<Promise<Result<number, Error>>>(Result.wrap(() => 1).promise())

declare let fnA: () => Promise<number> | number
expectType<Promise<Result<number, Error>>>(Result.wrap(fnA).promise())
expectType<Promise<Result<number, Error>>>(
  Result.wrap(fnA)
    .map(async (n) => 1 + (await n))
    .promise(),
)

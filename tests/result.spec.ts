import { Result } from '../src'
import { CustomError } from './common'

describe('Result', () => {
  test('and()', () => {
    const a = Result.Ok(1)
    const b = Result.Ok(2)
    const e = Result.Err(new Error())

    expect(a.and(b)).toEqual(b)
    expect(a.and(e)).toEqual(e)
    expect(e.and(a)).toEqual(e)
  })

  test('andThen()', () => {
    const a = Result.Ok(1)
    const e = Result.Err(new Error()) as Result<number, Error>

    expect(a.andThen((n) => Result.Ok(n + 1))).toEqual(Result.Ok(2))
    expect(a.andThen(() => e)).toEqual(e)
    expect(e.andThen((n) => Result.Ok(n + 1))).toEqual(e)
  })

  test('err()', () => {
    expect(Result.Ok(1).err().isNone()).toBeTruthy()
    expect(Result.Err(1).err().isSome()).toBeTruthy()
  })

  test('expect()', () => {
    const e = Result.Err(new Error())

    expect(() => {
      Result.Ok(1).expect('unreachable')
    }).not.toThrow()

    expect(() => {
      e.expect('boom')
    }).toThrow()

    expect(() => {
      e.expect(new CustomError('custom error'))
    }).toThrow(CustomError)

    expect(() => {
      e.expect(() => new CustomError('custom error'))
    }).toThrow(CustomError)
  })

  test('expectErr()', () => {
    const a = Result.Ok(1)

    expect(() => {
      Result.Err(new Error()).expectErr('unreachable')
    }).not.toThrow()

    expect(() => {
      a.expectErr('boom')
    }).toThrow()

    expect(() => {
      a.expectErr(new CustomError('custom error'))
    }).toThrow(CustomError)

    expect(() => {
      a.expectErr(() => new CustomError('custom error'))
    }).toThrow(CustomError)
  })

  test('isErr() && Err.into()', () => {
    const e = Result.Err(0)

    expect(e.isErr()).toBe(true)

    // type guard
    if (e.isErr()) {
      expect(e.into()).toBe(0)
    }

    expect(Result.Ok(1).isErr()).toBe(false)
  })

  test('isOk() && Ok.into()', () => {
    const a = Result.Ok(1)

    expect(a.isOk()).toBe(true)

    // type guard
    if (a.isOk()) {
      expect(a.into()).toBe(1)
    }

    expect(Result.Err(0).isOk()).toBe(false)
  })

  test('iter()', () => {
    expect(Array.from(Result.Ok(1).iter())).toEqual([1])
    expect(Array.from(Result.Err(0).iter())).toEqual([])
  })

  test('map()', () => {
    const e = Result.Err(new Error()) as Result<number, Error>
    expect(Result.Ok(1).map((n) => n + 1)).toEqual(Result.Ok(2))
    expect(e.map((n) => n + 1)).toEqual(e)
  })

  test('mapErr()', () => {
    const a = Result.Ok(1)
    const e = Result.Err(new Error()) as Result<number, Error>

    expect(a.mapErr(() => 'no error')).toEqual(a)
    expect(e.mapErr(() => 'has error')).toEqual(Result.Err('has error'))
  })

  test('mapOr()', () => {
    expect(Result.Ok(1).mapOr(0, (n) => n + 1)).toBe(2)
    expect(Result.Err<number, string>('').mapOr(0, (n) => n + 1)).toBe(0)
  })

  test('mapOrElse()', () => {
    expect(
      Result.Ok(1).mapOrElse(
        () => 0,
        (n) => n + 1,
      ),
    ).toBe(2)
    expect(
      Result.Err<number, string>('').mapOrElse(
        () => 0,
        (n) => n + 1,
      ),
    ).toBe(0)
  })

  test('ok()', () => {
    expect(Result.Ok(1).ok().isSome()).toBeTruthy()
    expect(Result.Err(1).ok().isNone()).toBeTruthy()
  })

  test('or()', () => {
    const a = Result.Ok(1)
    const b = Result.Ok(2)
    const e = Result.Err<number, number>(0)

    expect(a.or(b)).toEqual(a)
    expect(e.or(a)).toEqual(a)
    expect(e.or(b).or(a)).toEqual(b)
  })

  test('orElse()', () => {
    const a = Result.Ok(1)
    const b = Result.Ok(2)
    const e = Result.Err<number, number>(0)

    expect(a.orElse(() => b)).toEqual(a)
    expect(e.orElse(() => a)).toEqual(a)
  })

  test('promise()', async () => {
    const a = Result.Ok(Promise.resolve(1))
    const b = Result.Ok(Promise.reject())
    const e = Result.Err<Promise<number>, number>(0)

    expect(await a.promise()).toEqual(Result.Ok(1))
    expect((await b.promise()).isErr()).toBeTruthy()
    expect((await e.promise()).isErr()).toBeTruthy()

    const x = Result.Ok(1)
    const z = Result.Err<number, number>(0)

    expect(await x.promise()).toEqual(Result.Ok(1))
    expect(await z.promise()).toEqual(Result.Err(0))
    expect(await z.promise()).toEqual(Result.Err(0))
  })

  test('unwrap()', () => {
    expect(Result.Ok(1).unwrap()).toBe(1)
    expect(() => Result.Err(0).unwrap()).toThrow()
  })

  test('unwrapErr()', () => {
    expect(() => Result.Ok(1).unwrapErr()).toThrow()
    expect(Result.Err(0).unwrapErr()).toBe(0)
  })

  test('unwrapErrUnchecked()', () => {
    expect(Result.Ok(1).unwrapErrUnchecked()).toBeUndefined()
    expect(Result.Err(0).unwrapErrUnchecked()).toBe(0)
  })

  test('unwrapOr()', () => {
    expect(Result.Ok(1).unwrapOr(2)).toBe(1)
    expect(Result.Err(0).unwrapOr(2)).toBe(2)
  })

  test('unwrapOrElse()', () => {
    expect(Result.Ok(1).unwrapOrElse(() => 2)).toBe(1)
    expect(Result.Err(0).unwrapOrElse(() => 2)).toBe(2)
  })

  test('unwrapUnchecked()', () => {
    expect(Result.Ok(1).unwrapUnchecked()).toBe(1)
    expect(Result.Err(0).unwrapUnchecked()).toBeUndefined()
  })

  test('static is()', () => {
    expect(Result.is(1)).toBeFalsy()
    expect(Result.is(Result.Ok(1))).toBeTruthy()
    expect(Result.is(Result.Err(0))).toBeTruthy()
  })

  test('static wrap()', async () => {
    // sync functions
    expect(Result.wrap(() => 1)).toEqual(Result.Ok(1))

    expect(
      Result.wrap(() => {
        throw new Error()
      }).isErr(),
    ).toBeTruthy()

    // async functions
    expect(await Result.wrap(async () => 1).promise()).toEqual(Result.Ok(1))

    expect(
      Result.wrap(async () => {
        throw 0
      }).isOk(),
    ).toBeTruthy()

    expect(
      await Result.wrap(async () => {
        throw 0
      }).promise(),
    ).toEqual(Result.Err(0))

    expect(
      await Result.wrap(() => {
        return new Promise(() => {
          throw 0
        })
      }).promise(),
    ).toEqual(Result.Err(0))

    // chain async functions
    expect(
      await Result.wrap(async () => 1)
        .map(async (n) => 1 + (await n))
        .promise(),
    ).toEqual(Result.Ok(2))

    expect(
      await Result.wrap(async () => {
        throw 0
      })
        .map(async (n) => 1 + (await n))
        .promise(),
    ).toEqual(Result.Err(0))
  })
})

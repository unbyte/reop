import { Result } from '../src'
import { CustomError } from './common'

describe('Result', () => {
  const a = Result.Ok<number, number>(1)
  const b = Result.Ok<number, number>(2)
  const e = Result.Err<number, number>(0)

  test('and()', () => {
    expect(a.and(b)).toEqual(b)
    expect(a.and(e)).toEqual(e)
    expect(e.and(a)).toEqual(e)
  })

  test('async and()', async () => {
    expect(await a.async().and(b)).toEqual(b)
    expect(await a.async().and(e)).toEqual(e)
    expect(await e.async().and(a)).toEqual(e)
  })

  test('andThen()', () => {
    expect(a.andThen((n) => Result.Ok(n + 1))).toEqual(Result.Ok(2))
    expect(a.andThen(() => e)).toEqual(e)
    expect(e.andThen((n) => Result.Ok(n + 1))).toEqual(e)
  })

  test('async andThen()', async () => {
    // async
    expect(await a.async().andThen((n) => Result.Ok(n + 1))).toEqual(
      Result.Ok(2),
    )
    expect(await a.async().andThen(() => e)).toEqual(e)
    expect(await e.async().andThen((n) => Result.Ok(n + 1))).toEqual(e)
  })

  test('async()', async () => {
    expect(await a.async()).toEqual(a)
    expect((await e.async()).isErr()).toBeTruthy()

    expect(await Result.Ok(Promise.resolve(1)).async()).toEqual(Result.Ok(1))
    expect(await Result.Ok(Promise.reject(0)).async()).toEqual(Result.Err(0))
  })

  test('async await()', async () => {
    expect(Result.Ok(Promise.resolve(1)).async().await()).toBeInstanceOf(
      Promise,
    )
  })

  test('err()', () => {
    expect(a.err().isNone()).toBeTruthy()
    expect(e.err().isSome()).toBeTruthy()
  })

  test('async err()', async () => {
    expect((await a.async().err()).isNone()).toBeTruthy()
    expect((await e.async().err()).isSome()).toBeTruthy()
  })

  test('expect()', () => {
    expect(() => {
      a.expect('unreachable')
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

  test('async expect()', async () => {
    expect(await a.async().expect('unreachable')).toBe(1)

    await expect(e.async().expect('boom')).rejects.not.toBeUndefined()
    await expect(
      e.async().expect(new CustomError('custom error')),
    ).rejects.not.toBeUndefined()
    await expect(
      e.async().expect(() => new CustomError('custom error')),
    ).rejects.not.toBeUndefined()
  })

  test('expectErr()', () => {
    expect(() => {
      e.expectErr('unreachable')
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

  test('async expectErr()', async () => {
    // async
    await expect(
      e.async().expectErr('unreachable'),
    ).resolves.not.toBeUndefined()

    await expect(a.async().expectErr('boom')).rejects.not.toBeUndefined()

    await expect(
      a.async().expectErr(new CustomError('custom error')),
    ).rejects.not.toBeUndefined()

    await expect(
      a.async().expectErr(() => new CustomError('custom error')),
    ).rejects.not.toBeUndefined()
  })

  test('isErr() && Err.into()', () => {
    expect(e.isErr()).toBe(true)

    // type guard
    if (e.isErr()) {
      expect(e.into()).toBe(0)
    }

    expect(a.isErr()).toBe(false)
  })

  test('isOk() && Ok.into()', () => {
    expect(a.isOk()).toBe(true)

    // type guard
    if (a.isOk()) {
      expect(a.into()).toBe(1)
    }

    expect(e.isOk()).toBe(false)
  })

  test('iter()', () => {
    expect(Array.from(a.iter())).toEqual([1])
    expect(Array.from(e.iter())).toEqual([])
  })

  test('async iter()', async () => {
    expect(Array.from(await a.async().iter())).toEqual([1])
    expect(Array.from(await e.async().iter())).toEqual([])
  })

  test('map()', () => {
    expect(a.map((n) => n + 1)).toEqual(Result.Ok(2))
    expect(e.map((n) => n + 1)).toEqual(e)
  })

  test('async map()', async () => {
    expect(await a.async().map((n) => n + 1)).toEqual(Result.Ok(2))
    expect(await e.async().map((n) => n + 1)).toEqual(e)
  })

  test('mapErr()', () => {
    expect(a.mapErr(() => 'no error')).toEqual(a)
    expect(e.mapErr(() => 'has error')).toEqual(Result.Err('has error'))
  })

  test('async mapErr()', async () => {
    expect(await a.async().mapErr(() => 'no error')).toEqual(a)
    expect(await e.async().mapErr(() => 'has error')).toEqual(
      Result.Err('has error'),
    )
  })

  test('mapOr()', () => {
    expect(a.mapOr(0, (n) => n + 1)).toBe(2)
    expect(e.mapOr(0, (n) => n + 1)).toBe(0)
  })

  test('async mapOr()', async () => {
    expect(await a.async().mapOr(0, (n) => n + 1)).toBe(2)
    expect(await e.async().mapOr(0, (n) => n + 1)).toBe(0)
  })

  test('mapOrElse()', () => {
    expect(
      a.mapOrElse(
        () => 0,
        (n) => n + 1,
      ),
    ).toBe(2)
    expect(
      e.mapOrElse(
        () => 0,
        (n) => n + 1,
      ),
    ).toBe(0)
  })

  test('async mapOrElse()', async () => {
    expect(
      await a.async().mapOrElse(
        async () => 0,
        async (n) => n + 1,
      ),
    ).toBe(2)
    expect(
      await e.async().mapOrElse(
        () => 0,
        (n) => n + 1,
      ),
    ).toBe(0)
  })

  test('ok()', () => {
    expect(a.ok().isSome()).toBeTruthy()
    expect(e.ok().isNone()).toBeTruthy()
  })

  test('async ok()', async () => {
    expect((await a.async().ok()).isSome()).toBeTruthy()
    expect((await e.async().ok()).isNone()).toBeTruthy()
  })

  test('or()', () => {
    expect(a.or(b)).toEqual(a)
    expect(e.or(a)).toEqual(a)
    expect(e.or(b).or(a)).toEqual(b)
  })

  test('async or()', async () => {
    expect(await a.async().or(b)).toEqual(a)
    expect(await e.async().or(a)).toEqual(a)
    expect(await e.async().or(b).or(a)).toEqual(b)
  })

  test('orElse()', () => {
    expect(a.orElse(() => b)).toEqual(a)
    expect(e.orElse(() => a)).toEqual(a)
  })

  test('async orElse()', async () => {
    expect(await a.async().orElse(() => b)).toEqual(a)
    expect(await e.async().orElse(() => a)).toEqual(a)
  })

  test('unwrap()', () => {
    expect(a.unwrap()).toBe(1)
    expect(() => e.unwrap()).toThrow()
  })

  test('async unwrap()', async () => {
    expect(await a.async().unwrap()).toBe(1)
    await expect(e.async().unwrap()).rejects.not.toBeUndefined()
  })

  test('unwrapErr()', () => {
    expect(() => a.unwrapErr()).toThrow()
    expect(e.unwrapErr()).toBe(0)
  })

  test('async unwrapErr()', async () => {
    await expect(a.async().unwrapErr()).rejects.not.toBeUndefined()
    expect(await e.async().unwrapErr()).toBe(0)
  })

  test('unwrapErrUnchecked()', () => {
    expect(a.unwrapErrUnchecked()).toBeUndefined()
    expect(e.unwrapErrUnchecked()).toBe(0)
  })

  test('async unwrapErrUnchecked()', async () => {
    expect(await a.async().unwrapErrUnchecked()).toBeUndefined()
    expect(await e.async().unwrapErrUnchecked()).toBe(0)
  })

  test('unwrapOr()', () => {
    expect(a.unwrapOr(2)).toBe(1)
    expect(e.unwrapOr(2)).toBe(2)
  })

  test('async unwrapOr()', async () => {
    expect(await a.async().unwrapOr(2)).toBe(1)
    expect(await e.async().unwrapOr(2)).toBe(2)
  })

  test('unwrapOrElse()', () => {
    expect(a.unwrapOrElse(() => 2)).toBe(1)
    expect(e.unwrapOrElse(() => 2)).toBe(2)
  })

  test('async unwrapOrElse()', async () => {
    expect(await a.async().unwrapOrElse(async () => 2)).toBe(1)
    expect(await e.async().unwrapOrElse(() => 2)).toBe(2)
  })

  test('unwrapUnchecked()', () => {
    expect(a.unwrapUnchecked()).toBe(1)
    expect(e.unwrapUnchecked()).toBeUndefined()
  })

  test('async unwrapUnchecked()', async () => {
    expect(await a.async().unwrapUnchecked()).toBe(1)
    expect(await e.async().unwrapUnchecked()).toBeUndefined()
  })

  test('static is()', () => {
    expect(Result.is(1)).toBeFalsy()
    expect(Result.is(a)).toBeTruthy()
    expect(Result.is(e)).toBeTruthy()
  })

  test('static isAsync()', () => {
    expect(Result.isAsync(1)).toBeFalsy()
    expect(Result.isAsync(a.async())).toBeTruthy()
    expect(Result.isAsync(e.async())).toBeTruthy()
  })

  test('static from()', () => {
    expect(Result.from(async () => 1).isOk()).toBeTruthy()

    expect(Result.from(() => 1)).toEqual(Result.Ok(1))

    // rejected promise is also Ok
    expect(
      Result.from(async () => {
        throw new Error()
      }).isOk(),
    ).toBeTruthy()

    expect(
      Result.from(() => {
        throw new Error()
      }).isErr(),
    ).toBeTruthy()
  })

  test('static fromAsync()', async () => {
    expect(await Result.fromAsync(() => 1 as any)).toEqual(Result.Ok(1))

    expect(await Result.fromAsync(async () => 1)).toEqual(Result.Ok(1))

    expect(
      await Result.fromAsync(() => {
        throw 0
      }),
    ).toEqual(Result.Err(0))

    expect(
      await Result.fromAsync(async () => {
        throw 0
      }),
    ).toEqual(Result.Err(0))

    expect(
      await Result.fromAsync(() => {
        return new Promise(() => {
          throw 0
        })
      }),
    ).toEqual(Result.Err(0))

    // chain async functions
    expect(await Result.fromAsync(async () => 1).map((n) => 1 + n)).toEqual(
      Result.Ok(2),
    )

    expect(
      await Result.fromAsync(async () => {
        throw 0
      }).map((n) => 1 + n),
    ).toEqual(Result.Err(0))
  })
})

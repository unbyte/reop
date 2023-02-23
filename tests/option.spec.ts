import { Option } from '../src'
import { CustomError } from './common'

describe('Option', () => {
  const a = Option.Some(1)
  const b = Option.Some(2)

  test('and()', () => {
    expect(a.and(b)).toEqual(b)
    expect(a.and(Option.None)).toEqual(Option.None)

    expect(Option.None.and(a)).toEqual(Option.None)
  })

  test('async and()', async () => {
    expect(await a.async().and(b)).toEqual(b)
    expect(await a.async().and(Option.None)).toEqual(Option.None)

    expect(await Option.None.async().and(a)).toEqual(Option.None)
  })

  test('andThen()', () => {
    expect(a.andThen((n) => Option.Some(n + 1))).toEqual(Option.Some(2))
    expect(a.andThen(() => Option.None)).toEqual(Option.None)
    expect(Option.None.andThen((n) => Option.Some(n + 1))).toEqual(Option.None)
  })

  test('async andThen()', async () => {
    expect(await a.async().andThen((n) => Option.Some(n + 1))).toEqual(
      Option.Some(2),
    )
    expect(await a.async().andThen(() => Option.None)).toEqual(Option.None)
    expect(
      await Option.None.async().andThen((n) => Option.Some(n + 1)),
    ).toEqual(Option.None)
  })

  test('async()', async () => {
    const a = Option.Some(Promise.resolve(1))
    const b = Option.Some(Promise.reject())

    expect(await a.async()).toEqual(Option.Some(1))
    expect(await b.async()).toEqual(Option.None)
    expect(await Option.None.async()).toEqual(Option.None)
  })

  test('expect()', () => {
    expect(() => {
      Option.Some(1).expect('unreachable')
    }).not.toThrow()

    expect(() => {
      Option.None.expect('boom')
    }).toThrow()

    expect(() => {
      Option.None.expect(new CustomError('custom error'))
    }).toThrow(CustomError)

    expect(() => {
      Option.None.expect(() => new CustomError('custom error'))
    }).toThrow(CustomError)
  })

  test('async expect()', async () => {
    await expect(a.async().expect('unreachable')).resolves.not.toBeUndefined()

    await expect(Option.None.async().expect('boom')).rejects.not.toBeUndefined()

    await expect(
      Option.None.async().expect(new CustomError('custom error')),
    ).rejects.not.toBeUndefined()

    await expect(
      Option.None.async().expect(() => new CustomError('custom error')),
    ).rejects.not.toBeUndefined()
  })

  test('filter()', () => {
    expect(a.filter((n) => n > 1)).toEqual(Option.None)
    expect(a.filter((n) => n <= 1)).toEqual(a)
    expect(Option.None.filter(() => true)).toEqual(Option.None)
  })

  test('async filter()', async () => {
    expect(await a.async().filter(async (n) => n > 1)).toEqual(Option.None)
    expect(await a.async().filter(async (n) => n <= 1)).toEqual(a)
    expect(await Option.None.async().filter(() => true)).toEqual(Option.None)
  })

  test('flatten()', () => {
    const a = Option.Some(Option.Some(1))
    const b = Option.Some(Option.None)

    expect(a.flatten()).toEqual(Option.Some(1))
    expect(b.flatten()).toEqual(Option.None)
    expect(Option.None.flatten()).toEqual(Option.None)
  })

  test('isNone()', () => {
    expect(a.isNone()).toBe(false)
    expect(Option.None.isNone()).toBe(true)
  })

  test('isSome() && Some.into()', () => {
    expect(a.isSome()).toBe(true)

    // type guard
    if (a.isSome()) {
      expect(a.into()).toBe(1)
    }

    expect(Option.None.isSome()).toBe(false)
  })

  test('iter()', () => {
    expect(Array.from(a.iter())).toEqual([1])
    expect(Array.from(Option.None.iter())).toEqual([])
  })

  test('async iter()', async () => {
    expect(Array.from(await a.async().iter())).toEqual([1])
    expect(Array.from(await Option.None.async().iter())).toEqual([])
  })

  test('map()', () => {
    expect(a.map((n) => n + 1)).toEqual(Option.Some(2))
    expect(Option.None.map((n) => n + 1)).toEqual(Option.None)
  })

  test('async map()', async () => {
    expect(await a.async().map((n) => n + 1)).toEqual(Option.Some(2))
    expect(await Option.None.async().map((n) => n + 1)).toEqual(Option.None)
  })

  test('mapOr()', () => {
    expect(a.mapOr(0, (n) => n + 1)).toBe(2)
    expect(Option.None.mapOr(0, (n) => n + 1)).toBe(0)
  })

  test('async mapOr()', async () => {
    expect(await a.async().mapOr(0, (n) => n + 1)).toBe(2)
    expect(await Option.None.async().mapOr(0, (n) => n + 1)).toBe(0)
  })

  test('mapOrElse()', () => {
    expect(
      a.mapOrElse(
        () => 0,
        (n) => n + 1,
      ),
    ).toBe(2)
    expect(
      Option.None.mapOrElse(
        () => 0,
        (n) => n + 1,
      ),
    ).toBe(0)
  })

  test('async mapOrElse()', async () => {
    expect(
      await a.async().mapOrElse(
        () => 0,
        (n) => n + 1,
      ),
    ).toBe(2)
    expect(
      await Option.None.async().mapOrElse(
        () => 0,
        (n) => n + 1,
      ),
    ).toBe(0)
  })

  test('okOr()', () => {
    expect(a.okOr(new Error()).isOk()).toBeTruthy()
    expect(Option.None.okOr(new Error()).isErr()).toBeTruthy()
  })

  test('async okOr()', async () => {
    expect((await a.async().okOr(new Error())).isOk()).toBeTruthy()
    expect((await Option.None.async().okOr(new Error())).isErr()).toBeTruthy()
  })

  test('okOrElse()', () => {
    expect(a.okOrElse(() => new Error()).isOk()).toBeTruthy()
    expect(Option.None.okOrElse(() => new Error()).isErr()).toBeTruthy()
  })

  test('async okOrElse()', async () => {
    expect((await a.async().okOrElse(() => new Error())).isOk()).toBeTruthy()
    expect(
      (await Option.None.async().okOrElse(() => new Error())).isErr(),
    ).toBeTruthy()
  })

  test('or()', () => {
    expect(a.or(b)).toEqual(a)
    expect(Option.None.or(a)).toEqual(a)
    expect(Option.None.or(b).or(a)).toEqual(b)
  })

  test('async or()', async () => {
    expect(await a.async().or(b)).toEqual(a)
    expect(await Option.None.async().or(a)).toEqual(a)
    expect(await Option.None.async().or(b).or(a)).toEqual(b)
  })

  test('orElse()', () => {
    expect(a.orElse(() => b)).toEqual(a)
    expect(Option.None.orElse(() => a)).toEqual(a)
  })

  test('async orElse()', async () => {
    expect(await a.async().orElse(() => b)).toEqual(a)
    expect(await Option.None.async().orElse(() => a)).toEqual(a)
  })

  test('unwrap()', () => {
    expect(a.unwrap()).toBe(1)
    expect(() => Option.None.unwrap()).toThrow()
  })

  test('async unwrap()', async () => {
    expect(await a.async().unwrap()).toBe(1)
    await expect(Option.None.async().unwrap()).rejects.not.toBeUndefined()
  })

  test('unwrapOr()', () => {
    expect(a.unwrapOr(2)).toBe(1)
    expect(Option.None.unwrapOr(2)).toBe(2)
  })

  test('async unwrapOr()', async () => {
    expect(await a.async().unwrapOr(2)).toBe(1)
    expect(await Option.None.async().unwrapOr(2)).toBe(2)
  })

  test('unwrapOrElse()', () => {
    expect(a.unwrapOrElse(() => 2)).toBe(1)
    expect(Option.None.unwrapOrElse(() => 2)).toBe(2)
  })

  test('async unwrapOrElse()', async () => {
    expect(await a.async().unwrapOrElse(async () => 2)).toBe(1)
    expect(await Option.None.async().unwrapOrElse(() => 2)).toBe(2)
  })

  test('unwrapUnchecked()', () => {
    expect(a.unwrapUnchecked()).toBe(1)
    expect(Option.None.unwrapUnchecked()).toBeUndefined()
  })

  test('async unwrapUnchecked()', async () => {
    expect(await a.async().unwrapUnchecked()).toBe(1)
    expect(await Option.None.async().unwrapUnchecked()).toBeUndefined()
  })

  test('zip()', () => {
    expect(a.zip(b)).toEqual(Option.Some([1, 2]))
    expect(a.zip(Option.None)).toEqual(Option.None)
    expect(Option.None.zip(b)).toEqual(Option.None)
  })

  test('async zip()', async () => {
    expect(await a.async().zip(b.async())).toEqual(Option.Some([1, 2]))
    expect(await a.async().zip(Option.None.async())).toEqual(Option.None)
    expect(await Option.None.async().zip(b.async())).toEqual(Option.None)
  })

  test('static is()', () => {
    expect(Option.is(1)).toBeFalsy()
    expect(Option.is(a)).toBeTruthy()
    expect(Option.is(Option.None)).toBeTruthy()
  })

  test('static isAsync()', () => {
    expect(Option.isAsync(1)).toBeFalsy()
    expect(Option.isAsync(a.async())).toBeTruthy()
    expect(Option.isAsync(Option.None.async())).toBeTruthy()
  })

  test('static from()', () => {
    expect(Option.from(async () => 1).isSome()).toBeTruthy()

    expect(Option.from(() => 1)).toEqual(Option.Some(1))

    // rejected promise is also Some
    expect(
      Option.from(async () => {
        throw new Error()
      }).isSome(),
    ).toBeTruthy()

    expect(
      Option.from(() => {
        throw new Error()
      }),
    ).toEqual(Option.None)
  })

  test('static fromAsync()', async () => {
    expect(await Option.fromAsync(() => 1 as any)).toEqual(Option.Some(1))

    expect(
      await Option.fromAsync(() => {
        throw 0
      }),
    ).toEqual(Option.None)

    expect(await Option.fromAsync(async () => 1)).toEqual(Option.Some(1))

    expect(
      await Option.fromAsync(async () => {
        throw new Error()
      }),
    ).toEqual(Option.None)

    expect(
      await Option.fromAsync(() => {
        return new Promise(() => {
          throw new Error()
        })
      }),
    ).toEqual(Option.None)

    // chain async function
    expect(await Option.fromAsync(async () => 1).map((n) => 1 + n)).toEqual(
      Option.Some(2),
    )

    expect(
      await Option.fromAsync(async () => {
        throw new Error()
      }).map((n) => 1 + n),
    ).toEqual(Option.None)
  })
})

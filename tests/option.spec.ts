import { Option } from '../src'
import { CustomError } from './common'

describe('Option', () => {
  test('and()', () => {
    const a = Option.Some(1)
    const b = Option.Some(2)

    expect(a.and(b)).toEqual(b)
    expect(a.and(Option.None)).toEqual(Option.None)

    expect(Option.None.and(a)).toEqual(Option.None)
  })

  test('andThen()', () => {
    const a = Option.Some(1)

    expect(a.andThen((n) => Option.Some(n + 1))).toEqual(Option.Some(2))
    expect(a.andThen(() => Option.None)).toEqual(Option.None)
    expect(Option.None.andThen((n) => Option.Some(n + 1))).toEqual(Option.None)
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

  test('filter()', () => {
    const a = Option.Some(1)

    expect(a.filter((n) => n > 1)).toEqual(Option.None)
    expect(a.filter((n) => n <= 1)).toEqual(a)
    expect(Option.None.filter(() => true)).toEqual(Option.None)
  })

  test('flatten()', () => {
    const a = Option.Some(Option.Some(1))
    const b = Option.Some(Option.None)

    expect(a.flatten()).toEqual(Option.Some(1))
    expect(b.flatten()).toEqual(Option.None)
    expect(Option.None.flatten()).toEqual(Option.None)
  })

  test('isNone()', () => {
    expect(Option.Some(0).isNone()).toBe(false)
    expect(Option.None.isNone()).toBe(true)
  })

  test('isSome() && Some.into()', () => {
    const a = Option.Some(0)

    expect(a.isSome()).toBe(true)

    // type guard
    if (a.isSome()) {
      expect(a.into()).toBe(0)
    }

    expect(Option.None.isSome()).toBe(false)
  })

  test('iter()', () => {
    expect(Array.from(Option.Some(1).iter())).toEqual([1])
    expect(Array.from(Option.Some('1').iter())).toEqual(['1'])
    expect(Array.from(Option.None.iter())).toEqual([])
  })

  test('map()', () => {
    expect(Option.Some(1).map((n) => n + 1)).toEqual(Option.Some(2))
    expect(Option.None.map((n) => n + 1)).toEqual(Option.None)
  })

  test('mapOr()', () => {
    expect(Option.Some(1).mapOr(0, (n) => n + 1)).toBe(2)
    expect(Option.None.mapOr(0, (n) => n + 1)).toBe(0)
  })

  test('mapOrElse()', () => {
    expect(
      Option.Some(1).mapOrElse(
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

  test('okOr()', () => {
    expect(Option.Some(1).okOr(new Error()).isOk()).toBeTruthy()
    expect(Option.None.okOr(new Error()).isErr()).toBeTruthy()
  })

  test('okOrElse()', () => {
    expect(
      Option.Some(1)
        .okOrElse(() => new Error())
        .isOk(),
    ).toBeTruthy()
    expect(Option.None.okOrElse(() => new Error()).isErr()).toBeTruthy()
  })

  test('or()', () => {
    const a = Option.Some(1)
    const b = Option.Some(2)

    expect(a.or(b)).toEqual(a)
    expect(Option.None.or(a)).toEqual(a)
    expect(Option.None.or(b).or(a)).toEqual(b)
  })

  test('orElse()', () => {
    const a = Option.Some(1)
    const b = Option.Some(2)

    expect(a.orElse(() => b)).toEqual(a)
    expect(Option.None.orElse(() => a)).toEqual(a)
  })

  test('promise()', async () => {
    const a = Option.Some(Promise.resolve(1))
    const b = Option.Some(Promise.reject())

    expect(await a.promise()).toEqual(Option.Some(1))
    expect(await b.promise()).toEqual(Option.None)
    expect(await Option.None.promise()).toEqual(Option.None)
  })

  test('unwrap()', () => {
    expect(Option.Some(1).unwrap()).toBe(1)
    expect(() => Option.None.unwrap()).toThrow()
  })

  test('unwrapOr()', () => {
    expect(Option.Some(1).unwrapOr(2)).toBe(1)
    expect(Option.None.unwrapOr(2)).toBe(2)
  })

  test('unwrapOrElse()', () => {
    expect(Option.Some(1).unwrapOrElse(() => 2)).toBe(1)
    expect(Option.None.unwrapOrElse(() => 2)).toBe(2)
  })

  test('unwrapUnchecked()', () => {
    expect(Option.Some(1).unwrapUnchecked()).toBe(1)
    expect(Option.None.unwrapUnchecked()).toBeUndefined()
  })

  test('zip()', () => {
    const a = Option.Some(1)
    const b = Option.Some(2)

    expect(a.zip(b)).toEqual(Option.Some([1, 2]))
    expect(a.zip(Option.None)).toEqual(Option.None)
    expect(Option.None.zip(b)).toEqual(Option.None)
  })

  test('static is()', () => {
    expect(Option.is(1)).toBeFalsy()
    expect(Option.is(Option.None)).toBeTruthy()
    expect(Option.is(Option.Some(1))).toBeTruthy()
  })

  test('static wrap()', async () => {
    // sync functions
    expect(Option.wrap(() => 1)).toEqual(Option.Some(1))

    expect(
      Option.wrap(() => {
        throw new Error()
      }),
    ).toEqual(Option.None)

    // async functions
    expect(await Option.wrap(async () => 1).promise()).toEqual(Option.Some(1))

    expect(
      Option.wrap(async () => {
        throw new Error()
      }).isSome(),
    ).toBeTruthy()

    expect(
      await Option.wrap(async () => {
        throw new Error()
      }).promise(),
    ).toEqual(Option.None)

    expect(
      await Option.wrap(() => {
        return new Promise(() => {
          throw new Error()
        })
      }).promise(),
    ).toEqual(Option.None)

    // chain async function
    expect(
      await Option.wrap(async () => 1)
        .map(async (n) => 1 + (await n))
        .promise(),
    ).toEqual(Option.Some(2))

    expect(
      await Option.wrap(async () => {
        throw new Error()
      })
        .map(async (n) => 1 + (await n))
        .promise(),
    ).toEqual(Option.None)
  })
})

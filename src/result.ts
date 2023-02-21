import { Option } from './option'
import {
  createIteratorOn,
  getEmptyIterator,
  isFunction,
  isPromise,
  isString,
  noop,
  rewriteStackTrace,
} from './common'

/**
 * # Description
 *
 * `Result<T, E>` is the type used for returning and propagating errors.
 * It is an enum with the variants, `Ok`, representing success and containing a value,
 * and `Err`, representing error and containing an error value.
 *
 * Though Javascript has `throw` and `try` syntax already, `Result` is still useful because
 * it reflects the possible exception at the type level, and provides some helper methods to make coding easier.
 *
 * **Note** `Result` is built on the premise that users will respect the type system
 * provided by typescript as much as possible, so it doesn't do a lot of runtime checks.
 *
 * # Method Overview
 *
 * ## Querying the variant
 * The {@link isOk} and {@link isErr} methods return `true` if the `Result` is `Ok` or `Err`, respectively.
 *
 * ## Extracting the contained value
 * These methods extract the contained value in an `Result<T, E>` when it is the `Ok` variant.
 *
 * If the `Result` is `Err`:
 * - {@link expect} throws a custom error or an Error with a provided custom message
 * - {@link unwrap} throws a fixed Error
 * - {@link unwrapOr} returns the provided default value
 * - {@link unwrapOrElse} returns the result of evaluating the provided function
 *
 *
 * These methods extract the contained value in a `Result<T, E>` when it is the `Err` variant.
 *
 * If the `Result` is `Ok`:
 * - {@link expectErr} throws a custom error or an Error with a provided custom message
 * - {@link unwrapErr} throws a fixed Error
 *
 *
 * ## Transforming contained values
 * These methods transform `Result` to `Option`:
 *
 * - {@link err} transforms `Result<T, E>` into `Option<E>`, mapping `Err(e)` to `Some(e)` and `Ok(v)` to `None`
 * - {@link ok} transforms `Result<T, E>` into `Option<T>`, mapping `Ok(v)` to `Some(v)` and `Err(e)` to `None`
 *
 * This method transforms the contained value of the `Ok` variant:
 *
 * - {@link map} transforms `Result<T, E>` into `Result<U, E>` by applying the provided function
 * to the contained value of `Ok` and leaving `Err` values unchanged
 *
 * This method transforms the contained value of the Err variant:
 *
 * - {@link mapErr} transforms `Result<T, E>` into `Result<T, F>`
 * by applying the provided function to the contained value of `Err` and leaving `Ok` values unchanged
 *
 * These methods transform `Result<T, E>` to a value of a possibly different type `U`:
 *
 * - {@link mapOr} applies the provided function to the contained value of `Ok`,
 * or returns the provided default value if the `Result` is `Err`
 * - {@link mapOrElse} applies the provided function to the contained value of `Ok`,
 * or returns the result of evaluating the provided fallback function if the `Result` is `Err`
 *
 * ## Boolean operators
 * These methods treat the `Result` as a boolean value, where `Ok` acts like true and `Err` acts like false.
 * There are two categories of these methods:
 *   ones that take an `Result` as input, and ones that take a function as input (to be lazily evaluated).
 *
 * The {@link and} and {@link or} methods take another `Result` as input, and produce an `Result` as output.
 * The `and` method can produce a `Result<U, E>` value having a different inner type `U` than `Result<T, E>`.
 * The `or` method can produce a `Result<T, F>` value having a different error type `F` than `Result<T, E>`.
 *
 * | method  | self     | input     | output   |
 * |---------|----------|-----------|----------|
 * | `and` | `Err(e)` | (ignored) | `Err(e)` |
 * | `and` | `Ok(x)`  | `Err(d)`  | `Err(d)` |
 * | `and` | `Ok(x)`  | `Ok(y)`   | `Ok(y)`  |
 * | `or`  | `Err(e)` | `Err(d)`  | `Err(d)` |
 * | `or`  | `Err(e)` | `Ok(y)`   | `Ok(y)`  |
 * | `or`  | `Ok(x)`  | (ignored) | `Ok(x)`  |
 *
 * The {@link andThen} and {@link orElse} methods take a function as input,
 * and only evaluate the function when they need to produce a new value.
 * The `andThen` method can produce a `Result<U, E>` value having a different inner type `U` than `Result<T, E>`.
 * The `orElse` method can produce a `Result<T, F>` value having a different error type `F` than `Result<T, E>`.
 *
 * | method       | self     | function input | function result | output   |
 * |--------------|----------|----------------|-----------------|----------|
 * | `andThen` | `Err(e)` | (not provided) | (not evaluated) | `Err(e)` |
 * | `andThen` | `Ok(x)`  | `x`            | `Err(d)`        | `Err(d)` |
 * | `andThen` | `Ok(x)`  | `x`            | `Ok(y)`         | `Ok(y)`  |
 * | `orElse`  | `Err(e)` | `e`            | `Err(d)`        | `Err(d)` |
 * | `orElse`  | `Err(e)` | `e`            | `Ok(y)`         | `Ok(y)`  |
 * | `orElse`  | `Ok(x)`  | (not provided) | (not evaluated) | `Ok(x)`  |
 *
 *
 * ## Iterating over Result
 * A `Result` can be iterated over. This can be helpful if you need an iterator that is conditionally empty.
 * The iterator will either produce a single value (when the `Result` is `Ok`),
 * or produce no values (when the `Result` is `Err`).
 *
 * ```javascript
 * const err = Result.Err(new Error())
 * for (const v of err.iter()) {
 *   console.log('unreachable', v)
 * }
 *
 * const ok = Result.Ok(1)
 * for (const v of ok.iter()) {
 *   console.log(v) // 1
 * }
 * ```
 */
export interface Result<T, E> {
  /**
   * Returns {@link other} if the result is `Ok`, otherwise returns the `Err` value.
   *
   * Arguments passed to {@link and} are eagerly evaluated;
   * if you are passing the result of a function call,
   * it is recommended to use {@link andThen}, which is lazily evaluated.
   */
  and<U>(this: Result<T, E>, other: Result<U, E>): Result<U, E>

  /**
   * Calls {@link f} if the result is `Ok`, otherwise returns the `Err` value.
   *
   * This function can be used for control flow based on `Result` values.
   */
  andThen<U>(this: Result<T, E>, f: (v: T) => Result<U, E>): Result<U, E>

  /**
   * Converts from `Result<T, E>` to `Option<E>`.
   */
  err(this: Result<T, E>): Option<E>

  /**
   * When is `Ok`:
   * - returns the contained value.
   *
   * When is `Err`:
   * - throws with `new Error()` if the passed {@link message} is string
   * - throws the passed custom Error if the {@link message} is Error
   */
  expect(
    this: Result<T, E>,
    message: string | Error | ((err: E) => string | Error),
  ): T

  /**
   * When is `Err`:
   * - returns the contained value.
   *
   * When is `Ok`:
   * - throws with `new Error()` if the passed {@link message} is string
   * - throws the passed custom Error if the {@link message} is Error
   */
  expectErr(
    this: Result<T, E>,
    message: string | Error | (() => string | Error),
  ): E

  /**
   * Returns `true` if the result is `Err`.
   */
  isErr(this: Result<T, E>): this is Err<T, E>

  /**
   * Returns `true` if the result is `Ok`.
   */
  isOk(this: Result<T, E>): this is Ok<T, E>

  /**
   * Returns an iterator over the possibly contained value.
   *
   * The iterator yields one value if the result is `Ok`, otherwise none.
   */
  iter(this: Result<T, E>): IterableIterator<T>

  /**
   * Maps a `Result<T, E>` to `Result<U, E>` by applying a function to a contained `Ok` value,
   * leaving an `Err` value untouched.
   *
   * This function can be used to compose the results of two functions.
   */
  map<U>(this: Result<T, E>, f: (v: T) => U): Result<U, E>

  /**
   * Maps a `Result<T, E>` to `Result<T, F>` by applying a function to a contained `Err` value,
   * leaving an `Ok` value untouched.
   *
   * This function can be used to pass through a successful result while handling an error.
   */
  mapErr<F>(this: Result<T, E>, f: (e: E) => F): Result<T, F>

  /**
   * Returns the provided {@link def} (if `Err`), or applies a function to the contained value (if `Ok`),
   *
   * Arguments passed to {@link mapOr} are eagerly evaluated;
   * if you are passing the result of a function call,
   * it is recommended to use {@link mapOrElse}, which is lazily evaluated.
   */
  mapOr<U>(this: Result<T, E>, def: U, f: (v: T) => U): U

  /**
   * Maps a `Result<T, E>` to `U` by applying fallback function {@link def} to a contained `Err` value,
   * or function {@link f} to a contained `Ok` value.
   *
   * This function can be used to unpack a successful result while handling an error.
   */
  mapOrElse<U>(this: Result<T, E>, def: (err: E) => U, f: (v: T) => U): U

  /**
   * Converts from `Result<T, E>` to `Option<T>`.
   */
  ok(this: Result<T, E>): Option<T>

  /**
   * Returns {@link other} if the result is `Err`, otherwise returns the `Ok` value.
   *
   * Arguments passed to {@link or} are eagerly evaluated;
   * if you are passing the result of a function call,
   * it is recommended to use {@link orElse}, which is lazily evaluated.
   */
  or<F>(this: Result<T, E>, other: Result<T, F>): Result<T, F>

  /**
   * Calls {@link f} if the result is `Err`, otherwise returns the `Ok` value.
   *
   * This function can be used for control flow based on result values.
   */
  orElse<F>(this: Result<T, E>, f: (err: E) => Result<T, F>): Result<T, F>

  /**
   * Transforms the `Result` into a `Promise<Result>`.
   */
  promise<F = Error>(this: Result<T, E>): Promise<Result<Awaited<T>, E | F>>

  /**
   * Behaves like {@link expect}, but using a fixed error message when it is a `Err`.
   */
  unwrap(this: Result<T, E>): T

  /**
   * Behaves like {@link expectErr}, but using a fixed error message when it is a `Ok`.
   */
  unwrapErr(this: Result<T, E>): E

  /**
   * Returns the contained `Err` value, or `undefined` if it is a `Ok`.
   */
  unwrapErrUnchecked(this: Result<T, E>): E | undefined

  /**
   * Returns the contained `Ok` value or a provided {@link def}.
   *
   * Arguments passed to {@link unwrapOr} are eagerly evaluated;
   * if you are passing the result of a function call,
   * it is recommended to use {@link unwrapOrElse}, which is lazily evaluated.
   */
  unwrapOr(this: Result<T, E>, def: T): T

  /**
   * Returns the contained `Ok` value or computes it from a closure.
   */
  unwrapOrElse(this: Result<T, E>, def: (err: E) => T): T

  /**
   * Returns the contained `Ok` value, or `undefined` if it is a `Err`.
   */
  unwrapUnchecked(this: Result<T, E>): T | undefined
}

export interface Ok<T, E> extends Result<T, E> {
  into(this: Ok<T, E>): T
}

export interface Err<T, E> extends Result<T, E> {
  into(this: Err<T, E>): E
}

const Value = Symbol()

class OkImpl<T, E> implements Ok<T, E> {
  private readonly [Value]: T

  constructor(value: T) {
    this[Value] = value
  }

  and<U>(other: Result<U, E>): Result<U, E> {
    return other
  }

  andThen<U>(f: (v: T) => Result<U, E>): Result<U, E> {
    return f(this[Value])
  }

  err(): Option<E> {
    return Option.None
  }

  expect(message: string | Error | ((err: E) => Error)): T {
    return this[Value]
  }

  expectErr(
    message: string | Error | (() => Error),
    ref: unknown = this.expectErr,
  ): E {
    if (isFunction(message)) {
      throw rewriteStackTrace(message(), ref)
    } else if (isString(message)) {
      throw rewriteStackTrace(new Error(message), ref)
    } else {
      throw message
    }
  }

  into(): T {
    return this[Value]
  }

  isErr(): this is Err<T, E> {
    return false
  }

  isOk(): this is Ok<T, E> {
    return true
  }

  iter(): IterableIterator<T> {
    return createIteratorOn(this[Value])
  }

  map<U>(f: (v: T) => U): Result<U, E> {
    return new OkImpl(f(this[Value]))
  }

  mapErr<F>(f: (e: E) => F): Result<T, F> {
    return this as unknown as Result<T, F>
  }

  mapOr<U>(def: U, f: (v: T) => U): U {
    return f(this[Value])
  }

  mapOrElse<U>(def: (err: E) => U, f: (v: T) => U): U {
    return f(this[Value])
  }

  ok(): Option<T> {
    return Option.Some(this[Value])
  }

  or<F>(other: Result<T, F>): Result<T, F> {
    return this as unknown as Result<T, F>
  }

  orElse<F>(f: (err: E) => Result<T, F>): Result<T, F> {
    return this as unknown as Result<T, F>
  }

  promise<F>(): Promise<Result<Awaited<T>, E | F>> {
    if (isPromise(this[Value])) {
      return this[Value].then(
        (val) => new OkImpl(val) as Result<Awaited<T>, E>,
        (err) => new ErrImpl(err) as Result<Awaited<T>, F>,
      )
    }
    return Promise.resolve(this as Result<Awaited<T>, E>)
  }

  unwrap(): T {
    return this[Value]
  }

  unwrapErr(): E {
    return this.expectErr('expect an Err, but got an Ok', this.unwrapErr)
  }

  unwrapErrUnchecked(): E | undefined {
    return undefined
  }

  unwrapOr(def: T): T {
    return this[Value]
  }

  unwrapOrElse(def: (err: E) => T): T {
    return this[Value]
  }

  unwrapUnchecked(): T | undefined {
    return this[Value]
  }
}

class ErrImpl<T, E> implements Err<T, E> {
  private readonly [Value]: E

  constructor(err: E) {
    this[Value] = err
  }

  and<U>(other: Result<U, E>): Result<U, E> {
    return this as unknown as Result<U, E>
  }

  andThen<U>(f: (v: T) => Result<U, E>): Result<U, E> {
    return this as unknown as Result<U, E>
  }

  err(): Option<E> {
    return Option.Some(this[Value])
  }

  expect(
    message: string | Error | ((err: E) => Error),
    ref: unknown = this.expect,
  ): T {
    if (isFunction(message)) {
      throw rewriteStackTrace(message(this[Value]), ref)
    } else if (isString(message)) {
      throw rewriteStackTrace(
        new Error(message, {
          cause: this[Value],
        }),
        ref,
      )
    } else {
      throw message
    }
  }

  expectErr(message: string | Error | (() => Error)): E {
    return this[Value]
  }

  into(): E {
    return this[Value]
  }

  isErr(): this is Err<T, E> {
    return true
  }

  isOk(): this is Ok<T, E> {
    return false
  }

  iter(): IterableIterator<T> {
    return getEmptyIterator()
  }

  map<U>(f: (v: T) => U): Result<U, E> {
    return this as unknown as Result<U, E>
  }

  mapErr<F>(f: (e: E) => F): Result<T, F> {
    return new ErrImpl(f(this[Value]))
  }

  mapOr<U>(def: U, f: (v: T) => U): U {
    return def
  }

  mapOrElse<U>(def: (err: E) => U, f: (v: T) => U): U {
    return def(this[Value])
  }

  ok(): Option<T> {
    return Option.None
  }

  or<F>(other: Result<T, F>): Result<T, F> {
    return other
  }

  orElse<F>(f: (err: E) => Result<T, F>): Result<T, F> {
    return f(this[Value])
  }

  promise<F>(): Promise<Result<Awaited<T>, E>> {
    return Promise.resolve(this as Result<Awaited<T>, E>)
  }

  unwrap(): T {
    return this.expect('expect an Ok, but got an Err')
  }

  unwrapErr(): E {
    return this[Value]
  }

  unwrapErrUnchecked(): E | undefined {
    return this[Value]
  }

  unwrapOr(def: T): T {
    return def
  }

  unwrapOrElse(def: (err: E) => T): T {
    return def(this[Value])
  }

  unwrapUnchecked(): T | undefined {
    return undefined
  }
}

/**
 * The Result type.
 * See the interface {@link Result} for more.
 */
export const Result = {
  /**
   * Contains the success value
   */
  Ok: <T, E = Error>(value: T) => new OkImpl(value) as Result<T, E>,
  /**
   * Contains the error value
   */
  Err: <T, E>(err: E) => new ErrImpl(err) as Result<T, E>,
  /**
   * Check if a value is an `Result`
   */
  is: (val: unknown): val is Result<any, any> =>
    val instanceof OkImpl || val instanceof ErrImpl,
  /**
   * Get an `Result` from executing a closure.
   * Returns `Err` when the execution throws an Error.
   */
  wrap<T, E = Error>(fn: () => T): Result<T, E> {
    try {
      const result = fn()
      if (isPromise(result)) {
        result.catch(noop)
      }
      return new OkImpl(result)
    } catch (e) {
      return new ErrImpl(e as E)
    }
  },
} as const

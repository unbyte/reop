import { AsyncOption, AsyncOptionImpl, Option } from './option'
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
   * Transforms the `Result` into a `AsyncResult`.
   */
  async<F = Error>(this: Result<T, E>): AsyncResult<Awaited<T>, E | F>

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

/**
 * The result of type narrowing of {@link Result}.
 */
export interface Ok<T, E> extends Result<T, E> {
  /**
   * Get the inner value safely.
   */
  into(this: Ok<T, E>): T
}

/**
 * The result of type narrowing of {@link Result}.
 */
export interface Err<T, E> extends Result<T, E> {
  /**
   * Get the inner error safely.
   */
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

  async<F>(): AsyncResult<Awaited<T>, E | F> {
    if (isPromise(this[Value])) {
      return new AsyncResultImpl(
        this[Value].then(
          (val: Awaited<T>) => new OkImpl(val),
          (err: F) => new ErrImpl(err) as unknown as Result<Awaited<T>, F>,
        ),
      )
    }
    return new AsyncResultImpl(Promise.resolve(this as Result<Awaited<T>, E>))
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

  async<F>(): AsyncResult<Awaited<T>, E> {
    return new AsyncResultImpl(Promise.resolve(this as Result<Awaited<T>, E>))
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
 * Async version of {@link Result}.
 *
 * There are two ways to convert {@link AsyncResult} back to {@link Result}:
 * - {@link await} method returns a `Promise<Result<T, E>>`, or
 * - `await` {@link AsyncResult} directly because it is a Promise-like object.
 */
export interface AsyncResult<T, E> extends PromiseLike<Result<T, E>> {
  /**
   * Async version of {@link Result.and}.
   */
  and<U>(this: AsyncResult<T, E>, other: Result<U, E>): AsyncResult<U, E>

  /**
   * Async version of {@link Result.andThen}.
   */
  andThen<U>(
    this: AsyncResult<T, E>,
    f: (v: T) => Promise<Result<U, E>> | Result<U, E>,
  ): AsyncResult<U, E>

  /**
   * Transform the `AsyncResult` into a `Result`.
   */
  await(this: AsyncResult<T, E>): Promise<Result<T, E>>

  /**
   * Async version of {@link Result.err}.
   */
  err(this: AsyncResult<T, E>): AsyncOption<E>

  /**
   * Async version of {@link Result.expect}.
   */
  expect(
    this: AsyncResult<T, E>,
    message: string | Error | ((err: E) => Error),
  ): Promise<T>

  /**
   * Async version of {@link Result.expectErr}.
   */
  expectErr(
    this: AsyncResult<T, E>,
    message: string | Error | (() => Error),
  ): Promise<E>

  /**
   * Async version of {@link Result.iter}.
   */
  iter(this: AsyncResult<T, E>): Promise<IterableIterator<T>>

  /**
   * Async version of {@link Result.map}.
   */
  map<U>(
    this: AsyncResult<T, E>,
    f: (v: T) => Promise<U> | U,
  ): AsyncResult<U, E>

  /**
   * Async version of {@link Result.mapErr}.
   */
  mapErr<F>(
    this: AsyncResult<T, E>,
    f: (e: E) => Promise<F> | F,
  ): AsyncResult<T, F>

  /**
   * Async version of {@link Result.mapOr}.
   */
  mapOr<U>(
    this: AsyncResult<T, E>,
    def: U,
    f: (v: T) => Promise<U> | U,
  ): Promise<U>

  /**
   * Async version of {@link Result.mapOrElse}.
   */
  mapOrElse<U>(
    this: AsyncResult<T, E>,
    def: (err: E) => Promise<U> | U,
    f: (v: T) => Promise<U> | U,
  ): Promise<U>

  /**
   * Async version of {@link Result.ok}.
   */
  ok(this: AsyncResult<T, E>): AsyncOption<T>

  /**
   * Async version of {@link Result.or}.
   */
  or<F>(this: AsyncResult<T, E>, other: Result<T, F>): AsyncResult<T, F>

  /**
   * Async version of {@link Result.orElse}.
   */
  orElse<F>(
    this: AsyncResult<T, E>,
    f: (err: E) => Promise<Result<T, F>> | Result<T, F>,
  ): AsyncResult<T, F>

  /**
   * Async version of {@link Result.unwrap}.
   */
  unwrap(this: AsyncResult<T, E>): Promise<T>

  /**
   * Async version of {@link Result.unwrapErr}.
   */
  unwrapErr(this: AsyncResult<T, E>): Promise<E>

  /**
   * Async version of {@link Result.unwrapErrUnchecked}.
   */
  unwrapErrUnchecked(this: AsyncResult<T, E>): Promise<E | undefined>

  /**
   * Async version of {@link Result.unwrapOr}.
   */
  unwrapOr(this: AsyncResult<T, E>, def: T): Promise<T>

  /**
   * Async version of {@link Result.unwrapOrElse}.
   */
  unwrapOrElse(
    this: AsyncResult<T, E>,
    def: (err: E) => Promise<T> | T,
  ): Promise<T>

  /**
   * Async version of {@link Result.unwrapUnchecked}.
   */
  unwrapUnchecked(this: AsyncResult<T, E>): Promise<T | undefined>
}

export class AsyncResultImpl<T, E> implements AsyncResult<T, E> {
  private readonly [Value]: Promise<Result<T, E>>

  constructor(value: Promise<Result<T, E>>) {
    this[Value] = value
  }

  and<U>(other: Result<U, E>): AsyncResult<U, E> {
    return new AsyncResultImpl(this[Value].then((opt) => opt.and(other)))
  }

  andThen<U>(
    f: (v: T) => Promise<Result<U, E>> | Result<U, E>,
  ): AsyncResult<U, E> {
    // Promise awaits nested promises automatically
    // so `as any` is safe
    return new AsyncResultImpl(this[Value].then((opt) => opt.andThen(f as any)))
  }

  await(): Promise<Result<T, E>> {
    return this[Value]
  }

  err(): AsyncOption<E> {
    return new AsyncOptionImpl(this[Value].then((res) => res.err()))
  }

  expect(
    message: string | Error | ((err: E) => Error),
    ref = this.expect,
  ): Promise<T> {
    return this[Value].then((res) => {
      if (res instanceof OkImpl) return res.into()
      else if (res instanceof ErrImpl) return res.expect(message, ref)
      // unreachable
    })
  }

  expectErr(
    message: string | Error | (() => Error),
    ref = this.expectErr,
  ): Promise<E> {
    return this[Value].then((res) => {
      if (res instanceof ErrImpl) return res.into()
      else if (res instanceof OkImpl) return res.expectErr(message, ref)
      // unreachable
    })
  }

  iter(): Promise<IterableIterator<T>> {
    return this[Value].then((res) => res.iter())
  }

  map<U>(f: (v: T) => Promise<U> | U): AsyncResult<U, E> {
    return new AsyncResultImpl(
      this[Value].then(async (res) => {
        if (res.isOk()) return Result.Ok(await f(res.into()))
        return res as unknown as Result<U, E>
      }),
    )
  }

  mapErr<F>(f: (e: E) => Promise<F> | F): AsyncResult<T, F> {
    return new AsyncResultImpl(
      this[Value].then(async (res) => {
        if (res.isErr()) return Result.Err(await f(res.into()))
        return res as unknown as Result<T, F>
      }),
    )
  }

  mapOr<U>(def: U, f: (v: T) => Promise<U> | U): Promise<U> {
    return this[Value].then((res) => res.mapOr(def, f))
  }

  mapOrElse<U>(
    def: (err: E) => Promise<U> | U,
    f: (v: T) => Promise<U> | U,
  ): Promise<U> {
    return this[Value].then((res) => res.mapOrElse(def, f))
  }

  ok(): AsyncOption<T> {
    return new AsyncOptionImpl(this[Value].then((res) => res.ok()))
  }

  or<F>(other: Result<T, F>): AsyncResult<T, F> {
    return new AsyncResultImpl(this[Value].then((res) => res.or(other)))
  }

  orElse<F>(
    f: (err: E) => Promise<Result<T, F>> | Result<T, F>,
  ): AsyncResult<T, F> {
    // Promise awaits nested promises automatically
    // so `as any` is safe
    return new AsyncResultImpl(this[Value].then((res) => res.orElse(f as any)))
  }

  then<R>(
    onfulfilled?:
      | ((value: Result<T, E>) => PromiseLike<R> | R)
      | undefined
      | null,
  ): PromiseLike<R> {
    return this[Value].then(onfulfilled)
  }

  unwrap(): Promise<T> {
    return this.expect('expect an Ok, but got an Err', this.unwrap)
  }

  unwrapErr(): Promise<E> {
    return this.expectErr('expect an Err, but got an Ok', this.unwrapErr)
  }

  unwrapErrUnchecked(): Promise<E | undefined> {
    return this[Value].then((res) => res.unwrapErrUnchecked())
  }

  unwrapOr(def: T): Promise<T> {
    return this[Value].then((res) => res.unwrapOr(def))
  }

  unwrapOrElse(def: (err: E) => Promise<T> | T): Promise<T> {
    // Promise awaits nested promises automatically
    // so `as any` is safe
    return this[Value].then((res) => res.unwrapOrElse(def as any))
  }

  unwrapUnchecked(): Promise<T | undefined> {
    return this[Value].then((res) => res.unwrapUnchecked())
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
   * Check if a value is an `AsyncResult`
   */
  isAsync: (val: unknown): val is AsyncResult<any, any> =>
    val instanceof AsyncResultImpl,
  /**
   * Get a `Result` from executing a closure.
   * Returns `Err` if the execution throws an Error.
   */
  from<T, E = Error>(fn: () => T): Result<T, E> {
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
  /**
   * Get an `AsyncResult` from executing a closure.
   * Returns `Err` if the promise is rejected.
   */
  fromAsync<T, E = Error>(fn: () => Promise<T>): AsyncResult<T, E> {
    try {
      const result = fn()
      if (isPromise(result)) {
        return new AsyncResultImpl(
          result.then(
            (res) => Result.Ok(res),
            (err) => Result.Err(err),
          ),
        )
      }
      return new AsyncResultImpl(Promise.resolve(Result.Ok(result)))
    } catch (e) {
      return new AsyncResultImpl(Promise.resolve(Result.Err(e as E)))
    }
  },
} as const

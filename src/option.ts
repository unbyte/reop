import {
  rewriteStackTrace,
  isFunction,
  isString,
  getEmptyIterator,
  isPromise,
  noop,
  createIteratorOn,
} from './common'
import { AsyncResult, AsyncResultImpl, Result } from './result'

/**
 * # Description
 *
 * Type `Option` represents an optional value:
 * every `Option` is either `Some` and contains a value, or `None` and does not.
 *
 * Though Javascript has `null` and `undefined` already, `Option` is still useful because
 * it provides some helper methods to make coding easier.
 *
 * **Note** `Option` is built on the premise that users will respect the type system
 * provided by typescript as much as possible, so it doesn't do a lot of runtime checks.
 *
 * # Method Overview
 *
 * ## Querying the variant
 * The {@link isSome} and {@link isNone} methods return true if the `Option` is `Some` or `None`, respectively.
 *
 * ## Extracting the contained value
 * These methods extract the contained value in an `Option<T>` when it is the `Some` variant.
 *
 * If the `Option` is `None`:
 * - {@link expect} throws a custom error or an Error with a provided custom message
 * - {@link unwrap} throws a fixed Error
 * - {@link unwrapOr} returns the provided default value
 * - {@link unwrapOrElse} returns the result of evaluating the provided function
 *
 * If the `Option` is `Some`, typescript should hint that there is a method called {@link into},
 * that get the contained value directly.
 *
 *
 * ## Transforming contained values
 * These methods transform `Option` to `Result`:
 *
 * - {@link okOr} transforms `Some(v)` to `Ok(v)`, and `None` to `Err(err)` using the provided default err value
 * - {@link okOrElse} transforms `Some(v)` to `Ok(v)`, and `None` to a value of Err using the provided function
 *
 * These methods transform the `Some` variant:
 *
 * - {@link filter} calls the provided predicate function on the contained value t if the `Option` is `Some(t)`,
 * and returns `Some(t)` if the function returns true; otherwise, returns `None`
 * - {@link flatten} removes one level of nesting from an `Option<Option<T>>`
 * - {@link map} transforms `Option<T>` to `Option<U>` by applying the provided function to the contained value of `Some`
 * and leaving `None` values unchanged
 *
 * These methods transform `Option<T>` to a value of a possibly different type `U`:
 *
 * - {@link mapOr} applies the provided function to the contained value of `Some`,
 * or returns the provided default value if the `Option` is `None`
 * - {@link mapOrElse} applies the provided function to the contained value of `Some`,
 * or returns the result of evaluating the provided fallback function if the `Option` is `None`
 *
 * These methods combine the `Some` variants of two `Option` values:
 *
 * - {@link zip} returns `Some((s, o))` if it is `Some(s)` and the provided `Option` value is `Some(o)`;
 * otherwise, returns `None`
 *
 *
 * ## Boolean operators
 * These methods treat the `Option` as a boolean value, where `Some` acts like true and `None` acts like false.
 * There are two categories of these methods:
 *   ones that take an `Option` as input, and ones that take a function as input (to be lazily evaluated).
 *
 * The {@link and} and {@link or} methods take another `Option` as input, and produce an `Option` as output.
 * Only the {@link and} method can produce an `Option<U>` value having a different inner type `U` than `Option<T>`.
 *
 * | method  | this      | input     | output    |
 * |---------|-----------|-----------|-----------|
 * | `and` | `None`    | (ignored) | `None`    |
 * | `and` | `Some(x)` | `None`    | `None`    |
 * | `and` | `Some(x)` | `Some(y)` | `Some(y)` |
 * | `or`  | `None`    | `None`    | `None`    |
 * | `or`  | `None`    | `Some(y)` | `Some(y)` |
 * | `or`  | `Some(x)` | (ignored) | `Some(x)` |
 *
 * The {@link andThen} and {@link orElse} methods take a function as input,
 * and only evaluate the function when they need to produce a new value.
 * Only the {@link andThen} method can produce an `Option<U>` value having a different inner type `U` than `Option<T>`.
 *
 * | method       | this      | function input | function result | output    |
 * |--------------|-----------|----------------|-----------------|-----------|
 * | `andThen` | `None`    | (not provided) | (not evaluated) | `None`    |
 * | `andThen` | `Some(x)` | `x`            | `None`          | `None`    |
 * | `andThen` | `Some(x)` | `x`            | `Some(y)`       | `Some(y)` |
 * | `orElse`  | `None`    | (not provided) | `None`          | `None`    |
 * | `orElse`  | `None`    | (not provided) | `Some(y)`       | `Some(y)` |
 * | `orElse`  | `Some(x)` | (not provided) | (not evaluated) | `Some(x)` |
 *
 *
 * ## Iterating over Option
 * An `Option` can be iterated over by {@link iter}.
 * This can be helpful if you need an iterator that is conditionally empty.
 * The iterator will either produce a single value (when the `Option` is `Some`),
 * or produce no values (when the `Option` is `None`).
 *
 *
 * ## Async and await
 * An `Option` can be turned into an {@link AsyncOption}, with which you can treat
 * `Option<Promise<U>>` like `Option<U>`, using {@link async} method,
 * and {@link AsyncOption} can be turned back into an `Option` using [await]{@link AsyncOption.await} method.
 *
 * For more, see {@link AsyncOption}.
 */
export interface Option<T> {
  /**
   * Returns `None` if the option is `None`, otherwise returns {@link other}.
   *
   * Arguments passed to {@link and} are eagerly evaluated;
   * if you are passing the result of a function call,
   * it is recommended to use {@link andThen}, which is lazily evaluated.
   */
  and<U>(this: Option<T>, other: Option<U>): Option<U>

  /**
   * Returns `None` if the option is `None`,
   * otherwise calls `f` with the wrapped value and returns the result.
   *
   * Some languages call this operation flatmap.
   */
  andThen<U>(this: Option<T>, f: (v: T) => Option<U>): Option<U>

  /**
   * Transforms the `Option` into a `AsyncOption`.
   */
  async(this: Option<T>): AsyncOption<Awaited<T>>

  /**
   * When is `Some`:
   * - returns the contained value.
   *
   * When is `None`:
   * - throws with `new Error()` if the passed {@link message} is string
   * - throws the passed custom Error if the {@link message} is Error
   */
  expect(this: Option<T>, message: string | Error | (() => Error)): T

  /**
   * Returns `None` if the option is `None`,
   * otherwise calls {@link predicate} with the wrapped value and returns:
   * - `Some(t)` if {@link predicate} returns `true` (where `t` is the wrapped value), and
   * - `None` if {@link predicate} returns `false`.
   */
  filter(this: Option<T>, predicate: (v: T) => boolean): Option<T>

  /**
   * Converts from `Option<Option<T>>` to `Option<T>`.
   */
  flatten<U>(this: Option<Option<U>>): Option<U>

  /**
   * Returns `true` if the option is a `None` value.
   */
  isNone(this: Option<T>): this is None<T>

  /**
   * Returns `true` if the option is a `Some` value.
   */
  isSome(this: Option<T>): this is Some<T>

  /**
   * Returns an iterator over the possibly contained value.
   */
  iter(this: Option<T>): IterableIterator<T>

  /**
   * Maps an `Option<T>` to `Option<U>` by applying a function to a contained value.
   */
  map<U>(this: Option<T>, f: (v: T) => U): Option<U>

  /**
   * Returns the provided {@link def} if `None`,
   * or applies a function to the contained value if `Some`.
   *
   * Arguments passed to {@link mapOr} are eagerly evaluated;
   * if you are passing the result of a function call,
   * it is recommended to use {@link mapOrElse}, which is lazily evaluated.
   */
  mapOr<U>(this: Option<T>, def: U, f: (v: T) => U): U

  /**
   * Computes a default function result if `None`,
   * or applies a different function to the contained value if `Some`.
   */
  mapOrElse<U>(this: Option<T>, d: () => U, f: (v: T) => U): U

  /**
   * Transforms the `Option<T>` into a `Result<T, E>`,
   * mapping `Some(v)` to `Ok(v)` and `None` to `Err(err)`.
   *
   * Arguments passed to {@link okOr} are eagerly evaluated;
   * if you are passing the result of a function call,
   * it is recommended to use {@link okOrElse}, which is lazily evaluated.
   */
  okOr<E>(this: Option<T>, err: E): Result<T, E>

  /**
   * Transforms the `Option<T>` into a `Result<T, E>`,
   * mapping `Some(v)` to `Ok(v)` and `None` to `Err(err())`.
   */
  okOrElse<E>(this: Option<T>, err: () => E): Result<T, E>

  /**
   * Returns the option if it contains a value, otherwise returns {@link other}.
   *
   * Arguments passed to {@link or} are eagerly evaluated;
   * if you are passing the result of a function call,
   * it is recommended to use {@link orElse}, which is lazily evaluated.
   */
  or(this: Option<T>, other: Option<T>): Option<T>

  /**
   * Returns the option if it contains a value,
   * otherwise calls {@link other} and returns the result.
   */
  orElse(this: Option<T>, other: () => Option<T>): Option<T>

  /**
   * Behaves like {@link expect}, but using a fixed error message when it is a `None`.
   */
  unwrap(this: Option<T>): T

  /**
   * Returns the contained `Some` value or a provided {@link def}.
   *
   * Arguments passed to {@link unwrapOr} are eagerly evaluated;
   * if you are passing the result of a function call,
   * it is recommended to use {@link unwrapOrElse}, which is lazily evaluated.
   */
  unwrapOr(this: Option<T>, def: T): T

  /**
   * Returns the contained `Some` value or computes it from a closure.
   */
  unwrapOrElse(this: Option<T>, d: () => T): T

  /**
   * Returns the contained `Some` value, or `undefined` if it is a `None`.
   */
  unwrapUnchecked(this: Option<T>): T | undefined

  /**
   * Zips with another `Option`.
   *
   * If it is `Some(s)` and other is `Some(o)`, this method returns `Some([s, o])`.
   * Otherwise, `None` is returned.
   */
  zip<U>(this: Option<T>, other: Option<U>): Option<[T, U]>
}

/**
 * The result of type narrowing of {@link Result}.
 */
export interface None<T> extends Option<T> {}

/**
 * The result of type narrowing of {@link Result}.
 */
export interface Some<T> extends Option<T> {
  /**
   * Get the inner value safely.
   */
  into(this: Some<T>): T
}

const Value = Symbol()

class SomeImpl<T> implements Some<T> {
  private readonly [Value]: T
  constructor(value: T) {
    this[Value] = value
  }

  and<U>(other: Option<U>): Option<U> {
    return other
  }

  andThen<U>(f: (v: T) => Option<U>): Option<U> {
    return f(this[Value])
  }

  async(): AsyncOption<Awaited<T>> {
    if (isPromise(this[Value])) {
      return new AsyncOptionImpl(
        this[Value].then(
          (val) => new SomeImpl(val),
          () => Option.None,
        ),
      )
    }
    return new AsyncOptionImpl(Promise.resolve(this as Option<Awaited<T>>))
  }

  expect(message: string | Error | (() => string | Error)): T {
    return this[Value]
  }

  filter(predicate: (v: T) => boolean): Option<T> {
    if (predicate(this[Value])) return this
    return Option.None
  }

  flatten<U>(): Option<U> {
    // Note: we believe that the type guard will ensure this operation meets expectations
    return this[Value] as Option<U>
  }

  into(): T {
    return this[Value]
  }

  isNone(): this is None<T> {
    return false
  }

  isSome(): this is Some<T> {
    return true
  }

  iter(): IterableIterator<T> {
    return createIteratorOn(this[Value])
  }

  map<U>(f: (v: T) => U): Option<U> {
    return new SomeImpl(f(this[Value]))
  }

  mapOr<U>(def: U, f: (v: T) => U): U {
    return f(this[Value])
  }

  mapOrElse<U>(d: () => U, f: (v: T) => U): U {
    return f(this[Value])
  }

  okOr<E>(err: E): Result<T, E> {
    return Result.Ok(this[Value])
  }

  okOrElse<E>(err: () => E): Result<T, E> {
    return Result.Ok(this[Value])
  }

  or(other: Option<T>): Option<T> {
    return this
  }

  orElse(other: () => Option<T>): Option<T> {
    return this
  }

  unwrap(): T {
    return this[Value]
  }

  unwrapOr(def: T): T {
    return this[Value]
  }

  unwrapOrElse(d: () => T): T {
    return this[Value]
  }

  unwrapUnchecked(): T | undefined {
    return this[Value]
  }

  zip<U>(other: Option<U>): Option<[T, U]> {
    if (other.isSome()) return new SomeImpl([this[Value], other.into()])
    return Option.None
  }
}

class NoneImpl<T> implements None<T> {
  and<U>(other: Option<U>): Option<U> {
    return this as unknown as Option<U>
  }

  andThen<U>(f: (v: T) => Option<U>): Option<U> {
    return this as unknown as Option<U>
  }

  async(): AsyncOption<Awaited<T>> {
    return new AsyncOptionImpl(Promise.resolve(Option.None))
  }

  expect(
    message: string | Error | (() => Error),
    ref: unknown = this.expect,
  ): T {
    if (isFunction(message)) {
      throw rewriteStackTrace(message(), ref)
    } else if (isString(message)) {
      throw rewriteStackTrace(new Error(message), ref)
    } else {
      throw message
    }
  }

  filter(predicate: (v: T) => boolean): Option<T> {
    return this
  }

  flatten<U>(): Option<U> {
    return this as unknown as Option<U>
  }

  isNone(): this is None<T> {
    return true
  }

  isSome(): this is Some<T> {
    return false
  }

  iter(): IterableIterator<T> {
    return getEmptyIterator()
  }

  map<U>(f: (v: T) => U): Option<U> {
    return this as unknown as Option<U>
  }

  mapOr<U>(def: U, f: (v: T) => U): U {
    return def
  }

  mapOrElse<U>(d: () => U, f: (v: T) => U): U {
    return d()
  }

  okOr<E>(err: E): Result<T, E> {
    return Result.Err(err)
  }

  okOrElse<E>(err: () => E): Result<T, E> {
    return Result.Err(err())
  }

  or(other: Option<T>): Option<T> {
    return other
  }

  orElse(other: () => Option<T>): Option<T> {
    return other()
  }

  unwrap(): T {
    return this.expect('expect a Some, but got a None', this.unwrap)
  }

  unwrapOr(def: T): T {
    return def
  }

  unwrapOrElse(d: () => T): T {
    return d()
  }

  unwrapUnchecked(): T | undefined {
    return undefined
  }

  zip<U>(other: Option<U>): Option<[T, U]> {
    return Option.None
  }
}

/**
 * Async version of {@link Option}.
 *
 * There are two ways to convert {@link AsyncOption} back to {@link Option}:
 * - {@link await} method returns a `Promise<Option<T>>`, or
 * - `await` {@link AsyncOption} directly because it is a Promise-like object.
 */
export interface AsyncOption<T> extends PromiseLike<Option<T>> {
  /**
   * Async version of {@link Option.and}.
   */
  and<U>(this: AsyncOption<T>, other: Option<U>): AsyncOption<U>

  /**
   * Async version of {@link Option.andThen}.
   */
  andThen<U>(
    this: AsyncOption<T>,
    f: (v: T) => Promise<Option<U>> | Option<U>,
  ): AsyncOption<U>

  /**
   * Transform the `AsyncOption` into an `Option`.
   */
  await(this: AsyncOption<T>): Promise<Option<T>>

  /**
   * Async version of {@link Option.expect}.
   */
  expect(
    this: AsyncOption<T>,
    message: string | Error | (() => Error),
  ): Promise<T>

  /**
   * Async version of {@link Option.filter}.
   */
  filter(
    this: AsyncOption<T>,
    predicate: (v: T) => Promise<boolean> | boolean,
  ): AsyncOption<T>

  /**
   * Async version of {@link Option.iter}.
   */
  iter(this: AsyncOption<T>): Promise<IterableIterator<T>>

  /**
   * Async version of {@link Option.map}.
   */
  map<U>(this: AsyncOption<T>, f: (v: T) => Promise<U> | U): AsyncOption<U>

  /**
   * Async version of {@link Option.mapOr}.
   */
  mapOr<U>(
    this: AsyncOption<T>,
    def: U,
    f: (v: T) => Promise<U> | U,
  ): Promise<U>

  /**
   * Async version of {@link Option.mapOrElse}.
   */
  mapOrElse<U>(
    this: AsyncOption<T>,
    d: () => Promise<U> | U,
    f: (v: T) => Promise<U> | U,
  ): Promise<U>

  /**
   * Async version of {@link Option.okOr}.
   */
  okOr<E>(this: AsyncOption<T>, err: E): AsyncResult<T, E>

  /**
   * Async version of {@link Option.okOrElse}.
   */
  okOrElse<E>(
    this: AsyncOption<T>,
    err: () => Promise<E> | E,
  ): AsyncResult<T, E>

  /**
   * Async version of {@link Option.or}.
   */
  or(this: AsyncOption<T>, other: Option<T>): AsyncOption<T>

  /**
   * Async version of {@link Option.orElse}.
   */
  orElse(
    this: AsyncOption<T>,
    other: () => Promise<Option<T>> | Option<T>,
  ): AsyncOption<T>

  /**
   * Async version of {@link Option.unwrap}.
   */
  unwrap(this: AsyncOption<T>): Promise<T>

  /**
   * Async version of {@link Option.unwrapOr}.
   */
  unwrapOr(this: AsyncOption<T>, def: T): Promise<T>

  /**
   * Async version of {@link Option.unwrapOrElse}.
   */
  unwrapOrElse(this: AsyncOption<T>, d: () => Promise<T> | T): Promise<T>

  /**
   * Async version of {@link Option.unwrapUnchecked}.
   */
  unwrapUnchecked(this: AsyncOption<T>): Promise<T | undefined>

  /**
   * Async version of {@link Option.zip}.
   */
  zip<U>(this: AsyncOption<T>, other: AsyncOption<U>): AsyncOption<[T, U]>
}

export class AsyncOptionImpl<T> implements AsyncOption<T> {
  private readonly [Value]: Promise<Option<T>>

  constructor(value: Promise<Option<T>>) {
    this[Value] = value
  }

  and<U>(other: Option<U>): AsyncOption<U> {
    return new AsyncOptionImpl(this[Value].then((opt) => opt.and(other)))
  }

  andThen<U>(f: (v: T) => Promise<Option<U>> | Option<U>): AsyncOption<U> {
    // Promise awaits nested promises automatically
    // so `as any` is safe
    return new AsyncOptionImpl(this[Value].then((opt) => opt.andThen(f as any)))
  }

  await(): Promise<Option<T>> {
    return this[Value]
  }

  expect(
    message: string | Error | (() => Error),
    ref = this.expect,
  ): Promise<T> {
    return this[Value].then((opt: SomeImpl<T> | NoneImpl<T>) => {
      if (opt instanceof SomeImpl) return opt.into()
      return opt.expect(message, ref)
    })
  }

  filter(predicate: (v: T) => Promise<boolean> | boolean): AsyncOption<T> {
    return new AsyncOptionImpl(
      this[Value].then(async (opt) => {
        if (opt.isSome() && (await predicate(opt.into()))) {
          return opt
        }
        return Option.None
      }),
    )
  }

  iter(): Promise<IterableIterator<T>> {
    return this[Value].then((opt) => opt.iter())
  }

  map<U>(f: (v: T) => Promise<U> | U): AsyncOption<U> {
    return new AsyncOptionImpl(
      this[Value].then(async (opt) => {
        if (opt.isSome()) return Option.Some(await f(opt.into()))
        return Option.None
      }),
    )
  }

  mapOr<U>(def: U, f: (v: T) => Promise<U> | U): Promise<U> {
    return this[Value].then((opt) => opt.mapOr(def, f))
  }

  mapOrElse<U>(
    d: () => Promise<U> | U,
    f: (v: T) => Promise<U> | U,
  ): Promise<U> {
    return this[Value].then((opt) => opt.mapOrElse(d, f))
  }

  okOr<E>(err: E): AsyncResult<T, E> {
    return new AsyncResultImpl(this[Value].then((opt) => opt.okOr(err)))
  }

  okOrElse<E>(err: () => Promise<E> | E): AsyncResult<T, E> {
    // Promise awaits nested promises automatically
    // so `as any` is safe
    return new AsyncResultImpl(
      this[Value].then((opt) => opt.okOrElse(err as any)),
    )
  }

  or(other: Option<T>): AsyncOption<T> {
    return new AsyncOptionImpl(this[Value].then((opt) => opt.or(other)))
  }

  orElse(other: () => Promise<Option<T>> | Option<T>): AsyncOption<T> {
    // Promise awaits nested promises automatically
    // so `as any` is safe
    return new AsyncOptionImpl(
      this[Value].then((opt) => opt.orElse(other as any)),
    )
  }

  then<R>(
    onfulfilled?: ((value: Option<T>) => R | PromiseLike<R>) | undefined | null,
  ): PromiseLike<R> {
    return this[Value].then(onfulfilled)
  }

  unwrap(): Promise<T> {
    return this.expect('expect a Some, but got a None', this.unwrap)
  }

  unwrapOr(def: T): Promise<T> {
    return this[Value].then((opt) => opt.unwrapOr(def))
  }

  unwrapOrElse(d: () => Promise<T> | T): Promise<T> {
    // Promise awaits nested promises automatically
    // so `as any` is safe
    return this[Value].then((opt) => opt.unwrapOrElse(d as any))
  }

  unwrapUnchecked(): Promise<T | undefined> {
    return this[Value].then((opt) => opt.unwrapUnchecked())
  }

  zip<U>(other: AsyncOptionImpl<U>): AsyncOption<[T, U]> {
    return new AsyncOptionImpl(
      Promise.all([this[Value], other[Value]]).then(([a, b]) => a.zip(b)),
    )
  }
}

/**
 * See type {@link Option} for more.
 */
export namespace Option {
  /**
   * Some value of type `T`.
   */
  export function Some<T>(value: T): Option<T> {
    return new SomeImpl(value)
  }

  /**
   * No value.
   */
  export const None: Option<any> = new NoneImpl<any>()

  /**
   * Check if a value is an `Option`
   */
  export function is(val: unknown): val is Option<any> {
    return val instanceof SomeImpl || val instanceof NoneImpl
  }

  /**
   * Check if a value is an `AsyncOption`
   */
  export function isAsync(val: unknown): val is AsyncOption<any> {
    return val instanceof AsyncOptionImpl
  }

  /**
   * Get an `Option` from executing a closure.
   * Returns `None` if the execution throws an Error (the Error will be ignored).
   *
   * **Note** Passing an async closure should be avoided unless it's intended to,
   * because it always returns a `Some` as async closure always returns a `Promise`
   */
  export function from<T>(fn: () => T): Option<T> {
    try {
      const result = fn()
      if (isPromise(result)) {
        result.then(noop, noop)
      }
      return new SomeImpl(result)
    } catch {
      return Option.None
    }
  }

  /**
   * Get an `AsyncOption` from executing a closure.
   * Returns `None` if the promise is rejected (the Error will be ignored).
   */
  export function fromAsync<T>(fn: () => Promise<T> | T): AsyncOption<T> {
    try {
      const result = fn()
      if (isPromise(result)) {
        return new AsyncOptionImpl(
          result.then(
            (res) => Option.Some(res),
            () => Option.None,
          ),
        )
      }
      return new AsyncOptionImpl(Promise.resolve(Option.Some(result)))
    } catch {
      return new AsyncOptionImpl(Promise.resolve(Option.None))
    }
  }

  /**
   * Wraps a function to return an `Option`.
   *
   * **Note** Passing an async function should be avoided unless it's intended to,
   * because the wrapped function will always return a `Some`
   * as async function always returns a `Promise`
   */
  export function wrap<T, A extends any[] = any[]>(
    fn: (...args: A) => T,
  ): (...args: A) => Option<T> {
    return (...args) => Option.from(() => fn(...args))
  }

  /**
   * Wraps an async function to return an `AsyncOption`.
   */
  export function wrapAsync<T, A extends any[] = any[]>(
    fn: (...args: A) => Promise<T> | T,
  ): (...args: A) => AsyncOption<T> {
    return (...args) => Option.fromAsync(() => fn(...args))
  }
}

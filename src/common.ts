export function isFunction(v: unknown): v is Function {
  return typeof v === 'function'
}

export function isString(v: unknown): v is string {
  return typeof v === 'string'
}

export function isPromise(v: unknown): v is Promise<any> {
  return v instanceof Promise
}

export const rewriteStackTrace: (e: Error, ref: unknown) => Error =
  // V8-only API
  // see https://nodejs.org/api/errors.html#errorcapturestacktracetargetobject-constructoropt
  'captureStackTrace' in Error
    ? (e, ref) => {
        ;(Error as any).captureStackTrace(e, ref)
        return e
      }
    : /* istanbul ignore next */
      (e) => e

const EmptyArray: any[] = []

export function getEmptyIterator<T>(): IterableIterator<T> {
  return EmptyArray[Symbol.iterator]() as IterableIterator<T>
}

export function createIteratorOn<T>(value: T): IterableIterator<T> {
  return (function* () {
    yield value
  })()
}

export const noop = () => {}

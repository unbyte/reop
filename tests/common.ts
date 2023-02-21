export class CustomError extends Error {
  constructor(message: string) {
    super(message)
  }
}

export function expectType<T>(t: T) {}

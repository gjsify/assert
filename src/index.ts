// https://github.com/browserify/commonjs-assert/blob/master/assert.js
// Currently in sync with Node.js lib/assert.js
// https://github.com/nodejs/node/commit/2a51ae424a513ec9a6aa3466baa0cc1d55dd4f3b

// Originally from narwhal.js (http://narwhaljs.org)
// Copyright (c) 2009 Thomas Robinson <280north.com>
//
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the 'Software'), to
// deal in the Software without restriction, including without limitation the
// rights to use, copy, modify, merge, publish, distribute, sublicense, and/or
// sell copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED 'AS IS', WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
// ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
// WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

'use strict';

import { codes } from '@gjsify/node-internal';
import type TAssert from 'assert';
import type { AssertPredicate } from 'assert';

const {
  ERR_AMBIGUOUS_ARGUMENT,
  ERR_INVALID_ARG_TYPE,
  ERR_INVALID_ARG_VALUE,
  ERR_INVALID_RETURN_VALUE,
  ERR_MISSING_ARGS
} = codes;

import { inspect, types } from 'util';
import { isDeepEqual, isDeepStrictEqual } from '@gjsify/node-internal/lib/util/comparisons.js';
import { AssertionError } from '@gjsify/node-internal/lib/assertion_error.js';

const { isPromise, isRegExp } = types;
import callBoundIntrinsic from 'call-bind/callBound';
const RegExpPrototypeTest = callBoundIntrinsic('RegExp.prototype.test');

let warned = false;

const NO_EXCEPTION_SENTINEL = {};

// All of the following functions must throw an AssertionError
// when a corresponding condition is not met, with a message that
// may be undefined if not provided. All assertion methods provide
// both the actual and expected values to the assertion error for
// display purposes.

function innerFail(obj: any) {
  if (obj.message instanceof Error) throw obj.message;

  throw new AssertionError(obj);
}

/**
 * @since v0.1.21
 * @param [message='Failed']
 */
export function fail(message?: string | Error): never;
  /** @deprecated since v10.0.0 - use fail([message]) or other assert functions instead. */
export function fail(
  actual: unknown,
  expected: unknown,
  message?: string | Error,
  operator?: string,
  // tslint:disable-next-line:ban-types
  stackStartFn?: Function
): never;

export function fail(actual?: unknown, expected?: unknown, message?: string | Error, operator?: string, stackStartFn?: Function) {
  const argsLen = arguments.length;

  let internalMessage;
  if (argsLen === 0) {
    internalMessage = 'Failed';
  } else if (argsLen === 1) {
    message = actual as string | Error;
    actual = undefined;
  } else {
    if (warned === false) {
      warned = true;
      const warn = process.emitWarning ? process.emitWarning : console.warn.bind(console);
      warn(
        'assert.fail() with more than one argument is deprecated. ' +
          'Please use assert.strictEqual() instead or only pass a message.',
        'DeprecationWarning',
        'DEP0094'
      );
    }
    if (argsLen === 2)
      operator = '!=';
  }

  if (message instanceof Error) throw message;

  const errArgs: { actual: unknown, expected: unknown, operator: string, stackStartFn: Function, message?: string } = {
    actual,
    expected,
    operator: operator === undefined ? 'fail' : operator,
    stackStartFn: stackStartFn || fail,
  };
  if (message !== undefined) {
    errArgs.message = message;
  }
  const err = new AssertionError(errArgs);
  if (internalMessage) {
    err.message = internalMessage;
    err.generatedMessage = true;
  }
  throw err;
}

function innerOk(fn: Function, argLen: number, value: any, message: string | Error) {
  if (!value) {
    let generatedMessage = false;

    if (argLen === 0) {
      generatedMessage = true;
      message = 'No value argument passed to `assert.ok()`';
    } else if (message instanceof Error) {
      throw message;
    }

    const err = new AssertionError({
      actual: value,
      expected: true,
      message,
      operator: '==',
      stackStartFn: fn
    });
    err.generatedMessage = generatedMessage;
    throw err;
  }
}

// Pure assertion tests whether a value is truthy, as determined
// by !!value.

/**
 * @since v0.1.21
 */
export function ok(value: unknown, message?: string | Error): asserts value;
export function ok(...args: any[]) {
  innerOk(ok, args.length, args[0], args[1]);
}

// The assert module provides functions that throw
// AssertionError's when particular conditions are not met. The
// assert module must conform to the following interface.

const assert = ok as Partial<typeof TAssert>;

assert.fail = fail;

// The AssertionError is defined in internal/error.
assert.AssertionError = AssertionError;

assert.ok = ok;

/**
 * The equality assertion tests shallow, coercive equality with ==.
 * @since v0.1.21
 */
assert.equal  = function equal(actual: unknown, expected: unknown, message?: string | Error) {
  if (arguments.length < 2) {
    throw new ERR_MISSING_ARGS('actual', 'expected');
  }
  // eslint-disable-next-line eqeqeq
  if (actual != expected) {
    innerFail({
      actual,
      expected,
      message,
      operator: '==',
      stackStartFn: equal
    });
  }
};
export const equal = assert.equal;

/**
 * The non-equality assertion tests for whether two objects are not equal with !=.
 * @since v0.1.21
 */
assert.notEqual = function notEqual(actual: unknown, expected: unknown, message?: string | Error) {
  if (arguments.length < 2) {
    throw new ERR_MISSING_ARGS('actual', 'expected');
  }
  // eslint-disable-next-line eqeqeq
  if (actual == expected) {
    innerFail({
      actual,
      expected,
      message,
      operator: '!=',
      stackStartFn: notEqual
    });
  }
};
export const notEqual = assert.notEqual;

/**
 * The equivalence assertion tests a deep equality relation.
 * @since v0.1.21
 */
assert.deepEqual = function deepEqual(actual: unknown, expected: unknown, message?: string | Error) {
  if (arguments.length < 2) {
    throw new ERR_MISSING_ARGS('actual', 'expected');
  }
  if (!isDeepEqual(actual, expected)) {
    innerFail({
      actual,
      expected,
      message,
      operator: 'deepEqual',
      stackStartFn: deepEqual
    });
  }
};

export const deepEqual = assert.deepEqual ;

/**
 * The non-equivalence assertion tests for any deep inequality.
 * @since v0.1.21
 */
assert.notDeepEqual = function notDeepEqual(actual: unknown, expected: unknown, message?: string | Error) {
  if (arguments.length < 2) {
    throw new ERR_MISSING_ARGS('actual', 'expected');
  }
  if (isDeepEqual(actual, expected)) {
    innerFail({
      actual,
      expected,
      message,
      operator: 'notDeepEqual',
      stackStartFn: notDeepEqual
    });
  }
};
export const notDeepEqual = assert.notDeepEqual;

/**
 * Tests for deep equality between the `actual` and `expected` parameters.
 * "Deep" equality means that the enumerable "own" properties of child objects
 * are recursively evaluated also by the following rules.
 * @since v1.2.0
 */
assert.deepStrictEqual = function deepStrictEqual<T>(actual: unknown, expected: T, message?: string | Error): asserts actual is T {
  if (arguments.length < 2) {
    throw new ERR_MISSING_ARGS('actual', 'expected');
  }
  if (!isDeepStrictEqual(actual, expected)) {
    innerFail({
      actual,
      expected,
      message,
      operator: 'deepStrictEqual',
      stackStartFn: deepStrictEqual
    });
  }
};
export const deepStrictEqual = assert.deepStrictEqual;

/**
 * Tests for deep strict inequality. Opposite of {@link deepStrictEqual}.
 * @since v1.2.0
 */
assert.notDeepStrictEqual = function notDeepStrictEqual(actual: unknown, expected: unknown, message?: string | Error) {
  if (arguments.length < 2) {
    throw new ERR_MISSING_ARGS('actual', 'expected');
  }
  if (isDeepStrictEqual(actual, expected)) {
    innerFail({
      actual,
      expected,
      message,
      operator: 'notDeepStrictEqual',
      stackStartFn: notDeepStrictEqual
    });
  }
}
export const notDeepStrictEqual = assert.notDeepStrictEqual;

/**
 * Tests strict equality between the `actual` and `expected` parameters as
 * determined by [`Object.is()`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is).
 * @since v0.1.21
 */
assert.strictEqual = function strictEqual<T>(actual: unknown, expected: T, message?: string | Error): asserts actual is T {
  if (arguments.length < 2) {
    throw new ERR_MISSING_ARGS('actual', 'expected');
  }
  if (!Object.is(actual, expected)) {
    innerFail({
      actual,
      expected,
      message,
      operator: 'strictEqual',
      stackStartFn: strictEqual
    });
  }
};
export const strictEqual = assert.strictEqual;

/**
 * Tests strict inequality between the `actual` and `expected` parameters as
 * determined by [`Object.is()`](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Object/is).
 * @since v0.1.21
 */
assert.notStrictEqual = function notStrictEqual(actual: unknown, expected: unknown, message?: string | Error) {
  if (arguments.length < 2) {
    throw new ERR_MISSING_ARGS('actual', 'expected');
  }
  if (Object.is(actual, expected)) {
    innerFail({
      actual,
      expected,
      message,
      operator: 'notStrictEqual',
      stackStartFn: notStrictEqual
    });
  }
};
export const notStrictEqual = assert.notStrictEqual;

class Comparison {
  constructor(obj, keys, actual?) {
    keys.forEach(key => {
      if (key in obj) {
        if (actual !== undefined &&
          typeof actual[key] === 'string' &&
          isRegExp(obj[key]) &&
          RegExpPrototypeTest(obj[key], actual[key])
        ) {
          this[key] = actual[key];
        } else {
          this[key] = obj[key];
        }
      }
    });
  }
}

function compareExceptionKey(actual, expected, key, message, keys, fn) {
  if (!(key in actual) || !isDeepStrictEqual(actual[key], expected[key])) {
    if (!message) {
      // Create placeholder objects to create a nice output.
      const a = new Comparison(actual, keys);
      const b = new Comparison(expected, keys, actual);

      const err = new AssertionError({
        actual: a,
        expected: b,
        operator: 'deepStrictEqual',
        stackStartFn: fn
      });
      err.actual = actual;
      err.expected = expected;
      err.operator = fn.name;
      throw err;
    }
    innerFail({
      actual,
      expected,
      message,
      operator: fn.name,
      stackStartFn: fn
    });
  }
}

function expectedException(actual, expected, msg?, fn?) {
  if (typeof expected !== 'function') {
    if (isRegExp(expected))
      return RegExpPrototypeTest(expected, actual);
    // assert.doesNotThrow does not accept objects.
    if (arguments.length === 2) {
      throw new ERR_INVALID_ARG_TYPE(
        'expected', ['Function', 'RegExp'], expected
      );
    }

    // Handle primitives properly.
    if (typeof actual !== 'object' || actual === null) {
      const err = new AssertionError({
        actual,
        expected,
        message: msg,
        operator: 'deepStrictEqual',
        stackStartFn: fn
      });
      err.operator = fn.name;
      throw err;
    }

    const keys = Object.keys(expected);
    // Special handle errors to make sure the name and the message are compared
    // as well.
    if (expected instanceof Error) {
      keys.push('name', 'message');
    } else if (keys.length === 0) {
      throw new ERR_INVALID_ARG_VALUE('error',
                                      expected, 'may not be an empty object');
    }
    keys.forEach(key => {
      if (
        typeof actual[key] === 'string' &&
        isRegExp(expected[key]) &&
        RegExpPrototypeTest(expected[key], actual[key])
      ) {
        return;
      }
      compareExceptionKey(actual, expected, key, msg, keys, fn);
    });
    return true;
  }
  // Guard instanceof against arrow functions as they don't have a prototype.
  if (expected.prototype !== undefined && actual instanceof expected) {
    return true;
  }
  if (Error.isPrototypeOf(expected)) {
    return false;
  }
  return expected.call({}, actual) === true;
}

function getActual(fn) {
  if (typeof fn !== 'function') {
    throw new ERR_INVALID_ARG_TYPE('fn', 'Function', fn);
  }
  try {
    fn();
  } catch (e) {
    return e;
  }
  return NO_EXCEPTION_SENTINEL;
}

function checkIsPromise(obj) {
  // Accept native ES6 promises and promises that are implemented in a similar
  // way. Do not accept thenables that use a function as `obj` and that have no
  // `catch` handler.

  // TODO: thenables are checked up until they have the correct methods,
  // but according to documentation, the `then` method should receive
  // the `fulfill` and `reject` arguments as well or it may be never resolved.

  return isPromise(obj) ||
    obj !== null && typeof obj === 'object' &&
    typeof obj.then === 'function' &&
    typeof obj.catch === 'function';
}

function waitForActual(promiseFn) {
  return Promise.resolve().then(() => {
    let resultPromise;
    if (typeof promiseFn === 'function') {
      // Return a rejected promise if `promiseFn` throws synchronously.
      resultPromise = promiseFn();
      // Fail in case no promise is returned.
      if (!checkIsPromise(resultPromise)) {
        throw new ERR_INVALID_RETURN_VALUE('instance of Promise',
        'promiseFn', resultPromise);
      }
    } else if (checkIsPromise(promiseFn)) {
      resultPromise = promiseFn;
    } else {
      throw new ERR_INVALID_ARG_TYPE('promiseFn', ['Function', 'Promise'], promiseFn);
    }

    return Promise.resolve().then(() => resultPromise)
      .then(() => NO_EXCEPTION_SENTINEL)
      .catch(e => e);
  });
}

function expectsError(stackStartFn, actual, error, message) {
  if (typeof error === 'string') {
    if (arguments.length === 4) {
      throw new ERR_INVALID_ARG_TYPE('error',
                                     ['Object', 'Error', 'Function', 'RegExp'],
                                     error);
    }
    if (typeof actual === 'object' && actual !== null) {
      if (actual.message === error) {
        throw new ERR_AMBIGUOUS_ARGUMENT(
          'error/message',
          `The error message "${actual.message}" is identical to the message.`
        );
      }
    } else if (actual === error) {
      throw new ERR_AMBIGUOUS_ARGUMENT(
        'error/message',
        `The error "${actual}" is identical to the message.`
      );
    }
    message = error;
    error = undefined;
  } else if (error != null &&
             typeof error !== 'object' &&
             typeof error !== 'function') {
    throw new ERR_INVALID_ARG_TYPE('error',
                                   ['Object', 'Error', 'Function', 'RegExp'],
                                   error);
  }

  if (actual === NO_EXCEPTION_SENTINEL) {
    let details = '';
    if (error && error.name) {
      details += ` (${error.name})`;
    }
    details += message ? `: ${message}` : '.';
    const fnType = stackStartFn.name === 'rejects' ? 'rejection' : 'exception';
    innerFail({
      actual: undefined,
      expected: error,
      operator: stackStartFn.name,
      message: `Missing expected ${fnType}${details}`,
      stackStartFn
    });
  }
  if (error && !expectedException(actual, error, message, stackStartFn)) {
    throw actual;
  }
}

function expectsNoError(stackStartFn, actual, error, message) {
  if (actual === NO_EXCEPTION_SENTINEL)
    return;

  if (typeof error === 'string') {
    message = error;
    error = undefined;
  }

  if (!error || expectedException(actual, error)) {
    const details = message ? `: ${message}` : '.';
    const fnType = stackStartFn.name === 'doesNotReject' ?
      'rejection' : 'exception';
    innerFail({
      actual,
      expected: error,
      operator: stackStartFn.name,
      message: `Got unwanted ${fnType}${details}\n` +
               `Actual message: "${actual && actual.message}"`,
      stackStartFn
    });
  }
  throw actual;
}

/**
 * Expects the function `fn` to throw an error.
 * @since v0.1.21
 */
export function throws(block: () => unknown, message?: string | Error): void;
export function throws(block: () => unknown, error: AssertPredicate, message?: string | Error): void;
export function throws(promiseFn: () => unknown, ...args: any[]) {
  expectsError(throws, getActual(promiseFn), args[0], args[1]);
};
assert.throws = throws;

/**
 * Awaits the `asyncFn` promise or, if `asyncFn` is a function, immediately
 * calls the function and awaits the returned promise to complete. It will then
 * check that the promise is rejected.
 *
 * @since v10.0.0
 */
export async function rejects(block: (() => Promise<unknown>) | Promise<unknown>, message?: string | Error): Promise<void>;
export async function rejects(block: (() => Promise<unknown>) | Promise<unknown>, error: AssertPredicate, message?: string | Error): Promise<void>;
export async function rejects(promiseFn: (() => Promise<unknown>) | Promise<unknown>, ...args: any[]) {
  return waitForActual(promiseFn).then(result => {
    return expectsError(rejects, result, args[0], args[1]);
  });
}
assert.rejects = rejects;

/**
 * Asserts that the function `fn` does not throw an error.
 *
 * @since v0.1.21
 */
export function doesNotThrow(block: () => unknown, message?: string | Error): void;
export function doesNotThrow(block: () => unknown, error: AssertPredicate, message?: string | Error): void;
export function doesNotThrow(fn: () => unknown, ...args: any[]) {
  expectsNoError(doesNotThrow, getActual(fn), args[0], args[1]);
}
assert.doesNotThrow = doesNotThrow;

/**
 * Awaits the `asyncFn` promise or, if `asyncFn` is a function, immediately
 * calls the function and awaits the returned promise to complete. It will then
 * check that the promise is not rejected.
 *
 * @since v10.0.0
 */
export async function doesNotReject(block: (() => Promise<unknown>) | Promise<unknown>, message?: string | Error): Promise<void>;
export async function doesNotReject(block: (() => Promise<unknown>) | Promise<unknown>, error: AssertPredicate, message?: string | Error): Promise<void>;
export async function doesNotReject(fn: (() => Promise<unknown>) | Promise<unknown>, ...args: any[]) {
  return waitForActual(fn).then(result => {
    return expectsNoError(doesNotReject, result, args[0], args[1]);
  });
}
assert.doesNotReject = doesNotReject;

/**
 * Throws `value` if `value` is not `undefined` or `null`. This is useful when
 * testing the `error` argument in callbacks. The stack trace contains all frames
 * from the error passed to `ifError()` including the potential new frames for`ifError()` itself.
 *
 * @since v0.1.97
 */
export function ifError(value: unknown): asserts value is null | undefined;
export function ifError(err: Error): asserts err is null | undefined {
  if (err !== null && err !== undefined) {
    let message = 'ifError got unwanted exception: ';
    if (typeof err === 'object' && typeof err.message === 'string') {
      if (err.message.length === 0 && err.constructor) {
        message += err.constructor.name;
      } else {
        message += err.message;
      }
    } else {
      message += inspect(err);
    }

    const newErr = new AssertionError({
      actual: err,
      expected: null,
      operator: 'ifError',
      message,
      stackStartFn: ifError
    });

    // Make sure we actually have a stack trace!
    const origStack = err.stack;

    if (typeof origStack === 'string') {
      // This will remove any duplicated frames from the error frames taken
      // from within `ifError` and add the original error frames to the newly
      // created ones.
      const tmp2 = origStack.split('\n');
      tmp2.shift();
      // Filter all frames existing in err.stack.
      let tmp1 = newErr.stack.split('\n');
      for (var i = 0; i < tmp2.length; i++) {
        // Find the first occurrence of the frame.
        const pos = tmp1.indexOf(tmp2[i]);
        if (pos !== -1) {
          // Only keep new frames.
          tmp1 = tmp1.slice(0, pos);
          break;
        }
      }
      newErr.stack = `${tmp1.join('\n')}\n${tmp2.join('\n')}`;
    }

    throw newErr;
  }
}
assert.ifError = ifError;

// Currently in sync with Node.js lib/assert.js
// https://github.com/nodejs/node/commit/2a871df3dfb8ea663ef5e1f8f62701ec51384ecb
function internalMatch(string, regexp, message, fn, fnName) {
  if (!isRegExp(regexp)) {
    throw new ERR_INVALID_ARG_TYPE(
      'regexp', 'RegExp', regexp
    );
  }
  const match = fnName === 'match';
  if (typeof string !== 'string' ||
      RegExpPrototypeTest(regexp, string) !== match) {
    if (message instanceof Error) {
      throw message;
    }

    const generatedMessage = !message;

    // 'The input was expected to not match the regular expression ' +
    message = message || (typeof string !== 'string' ?
      'The "string" argument must be of type string. Received type ' +
        `${typeof string} (${inspect(string)})` :
      (match ?
        'The input did not match the regular expression ' :
        'The input was expected to not match the regular expression ') +
          `${inspect(regexp)}. Input:\n\n${inspect(string)}\n`);
    const err = new AssertionError({
      actual: string,
      expected: regexp,
      message,
      operator: fnName,
      stackStartFn: fn
    });
    err.generatedMessage = generatedMessage;
    throw err;
  }
}

assert.match = function match(string, regexp, message) {
  internalMatch(string, regexp, message, match, 'match');
};
export const match = assert.match;

assert.doesNotMatch = function doesNotMatch(string, regexp, message) {
  internalMatch(string, regexp, message, doesNotMatch, 'doesNotMatch');
};
export const doesNotMatch = assert.doesNotMatch;

// Expose a strict only variant of assert
function strict(...args: any[]) {
  innerOk(strict, args.length, args[0], args[1]);
}

(assert as any).strict = Object.assign(strict, assert, {
  equal: assert.strictEqual,
  deepEqual: assert.deepStrictEqual,
  notEqual: assert.notStrictEqual,
  notDeepEqual: assert.notDeepStrictEqual
});
assert.strict.strict = assert.strict;

export default (assert as typeof TAssert);

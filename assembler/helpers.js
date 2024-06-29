/* --{ THE HELPERS LIBRARY }--{ /assembler/helpers.js }---------------------- *

This tiny library exports a bunch of generic helper functions. */

export const put = console.log;

export const not = value => ! value;

export const iife = lambda => lambda();

export const tertiary = function(predicate, onTrue, onFalse, onNull) {

    /* This helper takes a ternary predicate and three arbitrary values.
    The helper returns the first value when the predicate is `true`, the
    second when it is `false`, and the third when it is `null`. */

    return predicate === null ? onNull : (predicate ? onTrue : onFalse);
};

export const stack = function(lambda) {

    /* This generic decorator automatically creates and returns a stack
    each time the decorated function is invoked. The `lambda` function
    gets `push` and `pop` helpers for accessing the stack prefixed to
    any arguments that are passed to it directly. The stack itself
    is bound to `this` inside the lambda.*/

    return (...args) => {

        const array = [];
        const push = arg => array.push(arg);
        const pop = () => array.pop();

        lambda.call(array, push, pop, ...args);

        return array;
    };
};

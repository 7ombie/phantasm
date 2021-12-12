/* --{ THE HELPERS LIBRARY }--{ /assembler/helpers.js }---------------------- *

This little library exports a bunch of generic functions that are useful
in almost every program. */

export const put = console.log;

export const not = value => ! value;

export const iife = lambda => lambda();

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

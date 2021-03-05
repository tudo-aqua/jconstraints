# jConstraints #
*jConstraints* is a library for modeling expressions
and for interacting with constraint solvers.

## Building and Installing ##

* In the *jConstraints* folder, run `./gradlew build`.
* If the compilation was successful, the *jConstraints* library is located at
  `jconstraints-core/build/libs/jconstraints-core-[VERSION].jar`.
* A fat JAR containing all dependencies can be found at: `build/libs/jconstraints-core-[VERSION]-all.jar`.

## How To Use ##

*jConstraints* does not come with constraint solvers.
In order to use it, you will have to install one
of the plugins that connect to constraint solvers.
On the [*tudo-aqua org*][9], you can find *jConstraints*
plugins for, e.g. Z3.

[1]: http://www.antlr3.org/
[3]: http://www.antlr3.org/license.html
[7]: https://code.google.com/p/guava-libraries/
[8]: http://www.apache.org/licenses/LICENSE-2.0
[9]: https://github.com/tudo-aqua

## About this fork ##
*jConstraints* has been founded by the [psycopaths](https://github.com/psycopaths).
We forked the original library and maintain it now in this fork.

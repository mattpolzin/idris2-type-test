
This project is very experimental. it may change in breaking ways and it may have bugs that make it unusable in situations I haven't tested yet.

# type-test

This is a fairly rudimentary attempt at the following goal: Write in-code
properties as either proofs or bespoke types. The latter get automatically run
as property based tests.

A proposition might be written in-code like:
```idris
test1 : (n : Integer) -> n - 1 + 1 === n
```

This proposition cannot be proven in-code without postulating some properties of
`Integer` subtraction/addition because these are primitive operations and the
`Integer` type is not defined inductively.

On the other hand, if we execute `test1` with any given input, we do expect the
property to hold. Property based testing can help us run that function many
times in a row with different integer inputs and check that the property holds
for all of those inputs. The `hedgehog` library offers such property based
testing.

`type-test` will run property based testing against propositions
that you can't or don't want to prove in code without you needing to drastically
change the in-code property.

You need to make the following small changes to the property so that `type-test`
knows to pick it up and test it.

1. Add a generator that produces `Integer` values. This is exactly the same
   generator the `hedgehog` project describes and documentation there will
   describe these generators in more detail.
2. Change the triple-equals (`===`) to `==>`. Define the function as
   constructing a test with `MkTTest`.

That looks like the following:
```idris
import Hedgehog
import TTest

%hint
int1000 : Gen Integer
int1000 = integer $ constant 0 1000

test1 : (n : Integer) -> n - 1 + 1 ==> n
test1 n = MkTTest
```

Next you run `type-test` in the folder of your project and it will test that
property 100 times:
```shell
$ type-test --find-ipkg ./src/IntegerTest.idr
  ✓ IntegerTest.test1 passed 100 tests.
```

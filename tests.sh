#!/bin/sh

# Simple commands

echo "Simple command"
echo hello > output.txt

# Pipelines

ls -l | grep foo

# For loop (strict POSIX)

for x in a b c; do
  echo "$x"
done

# For loop (test case, non-strict POSIX)

for x in a b c do echo $x done

# If statement

if test -z "$var"; then
  echo "empty"
elif test "$var" = "foo"; then
  echo "foo"
else
  echo "other"
fi

# While loop

while test "$i" -lt 5; do
  echo "$i"
done

# Until loop

until test "$i" -eq 0; do
  echo "$i"
done

# Case statement

case "$var" in
  foo) echo "Foo match" ;;
  bar) echo "Bar match" ;;
esac

# Function definition

myfunc() {
  echo "Function called"
}
myfunc

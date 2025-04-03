#!/bin/bash

echo "Compiling..."

gcc sh.c -o sh

if [ $? -eq 0 ]; then
  echo "OK"
else
  echo "ERROR: $?"
fi

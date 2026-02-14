#!/bin/bash

set -x

grep -rE '\<axiom|unsafe\>' atgt/

lake build

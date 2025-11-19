#!/bin/bash

for f in blueprint/web/sect*.html; do
    sed -i 's/✓/🐙/g' "$f"
done

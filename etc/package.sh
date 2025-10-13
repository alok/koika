#!/usr/bin/env bash

archive="koika-$(git rev-parse --short HEAD).tar.gz"
rm -f "$archive"
{ git ls-files -z; } | grep --null-data -v '^package.sh$' | \
    tar --create --gzip --file "$archive" --transform "s,^,koika/," --null --files-from=-
echo "creating $archive"

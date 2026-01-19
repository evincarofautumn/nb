MAKEFLAGS+=\
  --no-builtin-rules\
  --no-builtin-variables\
  --print-directory\
  --warn-undefined-variables

SHELL:=/bin/bash

.DEFAULT_GOAL:=all
.EXTRA_PREREQS:=$(MAKEFILE_LIST)
.RECIPEPREFIX:=;
.SHELLFLAGS:=\
  -O nullglob\
  -o errexit\
  -o pipefail\
  -c

# Directives

.DELETE_ON_ERROR:
.ONESHELL:

# Make

first-prerequisite=$<
prerequisite-set=$^
second-prerequisite=$(word 2,$(prerequisite-set))
stem=$*
target=$@

# Commands

#HD=hexdump $(hexdump-flags)
HD=xxd $(xxd-flags)

DIFF=colordiff $(diff-flags)
#DIFF=git diff $(git-diff-flags)

LINK=$(CC) $(LDFLAGS)

NB=./nb

# Flags

CC:=cc

CFLAGS:=

HDFLAGS:=

LDFLAGS:=

NBFLAGS:=

compile-flags:=\
  -Wall\
  -Wextra\
  -Wpedantic\
  \
  -Wno-overlength-strings\
  \
  -std=c23\

diff-flags:=\
  --expand-tabs\
  --side-by-side\
  --width=130

git-diff-flags:=\
  --anchored=\
  --diff-algorithm=minimal\
  --no-index\
  --unified=0

hexdump-flags:=\
  -e '4/1 "%02X" " " 4/1 "%02X" " " 4/1 "%02X" " " 4/1 "%02X" "\n"'

xxd-flags:=\
  -a\
  -g 4

# Recipes

compile-it=\
  $(CC)\
    $(compile-flags)\
    -c $(first-prerequisite)\
    -o $(target)\
    $(CFLAGS)

diff-them=\
  $(DIFF)\
    $(first-prerequisite)\
    $(second-prerequisite)

hexdump-it=\
  $(HD)\
    $(first-prerequisite)\
    >$(target)\
    $(HDFLAGS)

link-it=\
  $(LINK)\
    $(prerequisite-set)\
    -o $(target)

nb-it=\
  $(NB) $(target)

# Rules

.PHONY:all

  all:build
  .PHONY:build
  build:nb

    nb:nb.o;$(link-it)

      nb.o:nb.c;$(compile-it)

  all:test
  .PHONY:test
  test:want/reow.hex have/reow.hex;$(diff-them)

    want/reow.hex:want/reow.bin;$(hexdump-it)

      want/reow.bin:reow.o|@dir/want;$(link-it)

        reow.o:reow.c;$(compile-it)

    have/reow.hex:have/reow.bin;$(hexdump-it)

      have/reow.bin:nb|@dir/have;$(nb-it)

@phony:;

@dir/%:@phony;[[ -d $(stem) ]] || mkdir $(stem)

$(MAKEFILE_LIST)::;

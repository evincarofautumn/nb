# Primitives
################################################################

null=
space=$(null) $(null)
$(space)=$(null)
question-mark=?


# Make Flags
################################################################

MAKEFLAGS+=\
  --no-builtin-rules\
  --no-builtin-variables\
  --print-directory\
  --warn-undefined-variables

# Use Bash, not sh.
SHELL:=/bin/bash

# The default goal isn't necessarily the first in the file.
.DEFAULT_GOAL:=@default
.PHONY:@default

# Changing any of the makefiles causes a rebuild.
.EXTRA_PREREQS:=$(MAKEFILE_LIST)

# Don't require tab characters.
.RECIPEPREFIX:=;

# Bash flags.
.SHELLFLAGS:=\
  -O nullglob\
  -o errexit\
  -o pipefail\
  -c


# Make Directives
################################################################

# Delete possibly corrupt partial outputs on error.
.DELETE_ON_ERROR:

# Use a single shell invocation per recipe.
.ONESHELL:


# Make Aliases
################################################################

first-prerequisite=$<

prerequisite-bag=$+

prerequisite-set=$^

second-prerequisite=$(word 2,$(prerequisite-set))

stem=$*

target=$@


# Functions
################################################################

# Append $1 and $2,
# adding a space between them only if they're both nonempty.
space.2=$(if $1,$(if $2,$1$(space)$2,$1),$2)


# Commands
################################################################

CC:=cc

#HD=hexdump $(hexdump-flags)
HD=xxd $(xxd-flags)

DIFF=colordiff $(diff-flags)
#DIFF=git diff $(git-diff-flags)

LINK=$(call space.2,$(CC),$(LDFLAGS))

NB=./nb


# Extra Flags
################################################################

CFLAGS:=

HDFLAGS:=

LDFLAGS:=

NBFLAGS:=


# Required Flags
################################################################

compile-flags:=\
  -g\
  \
  -Wall\
  -Wextra\
  -Wpedantic\
  \
  -Werror=format\
  -Werror=return-type\
  \
  -Wno-extra-semi\
  -Wno-overlength-strings\
  \
  -std=c23

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
################################################################

# "it" means the first prerequisite.
# "them" means the prerequisite set or bag.

compile-it=\
  $(call space.2,$\
    $(CC)\
      $(compile-flags)\
      -c $(first-prerequisite)\
      -o $(target),$\
    $(CFLAGS))

diff-them=\
  $(DIFF)\
    $(first-prerequisite)\
    $(second-prerequisite)

hexdump-it=\
  $(call space.2,$\
    $(HD)\
      $(first-prerequisite)\
      >$(target),$\
    $(HDFLAGS))

link-it=\
  $(LINK)\
    $(prerequisite-bag)\
    -o $(target)

nb=\
  $(NB) $(target)


# Rules
################################################################

@default:@all

  @all:@build
  @build:nb

    nb:\
      nb.o\
      ;$(link-it)

      nb.o:\
        nb.c\
        ;$(compile-it)

  @all:@test
  @test:\
    want/reow.hex\
    have/reow.hex\
    ;$(diff-them)

    want/reow.hex:\
      want/reow.bin\
      ;$(hexdump-it)

      want/reow.bin:\
        reow.o\
        |@dir/want\
        ;$(link-it)

        reow.o:compile-flags:=
        reow.o:\
          reow.c\
          ;$(compile-it)

    have/reow.hex:\
      have/reow.bin\
      ;$(hexdump-it)

      have/reow.bin:\
        nb\
        |@dir/have\
        ;$(nb)


# Special Rules
################################################################

# A force target, allowing phony pattern rules.
@phony:;

# Marks all @-prefixed targets as phony.
@%:@phony

# Allows depending on whether a directory exists.
@dir/%:@phony;[[ -d $(stem) ]] || mkdir $(stem)

# Marks all makefiles as not needing to be rebuilt.
$(MAKEFILE_LIST)::;

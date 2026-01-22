# Primitives
################################################################

null=
space=$(null) $(null)
$(space)=$(null)
quotation-mark=$(firstword " ")
number-sign=\#
apostrophe=$(firstword ' ')
reverse-solidus=\\

define line-feed:=


endef

newline=$(line-feed)
backslash=$(reverse-solidus)

LF=$(newline)

else=$(null)
false=$(null)
true:=true


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

# Tells whether $1 and $2 are equal.
equal.2=$\
  $(if $(subst $1,$(null),$2),$\
    $(false),$\
  $(else)$(if $(subst $2,$(null),$1),$\
    $(false),$\
  $(else)$\
    $(true)))

# Returns $($1) if $1 is defined, otherwise returns $2.
get.2=$\
  $(if $(call equal.2,$(flavor $1),undefined),$\
    $2,$\
  $(else)$\
    $($1))

# Boolean negation.
not.1=$\
  $(if $(call equal.2,$1,$(true)),$\
    $(false),$\
  $(else)$(if $(call equal.2,$1,$(false)),$\
    $(true),$\
  $(else)$\
    $(error [$1]\:bool)))

# Quotes $1 for Bash.
quote.1=$\
  $(apostrophe)$\
  $(subst\
    $(LF),$\
    $(apostrophe)$$$(apostrophe)\n$(apostrophe)$(apostrophe),$\
    $(subst\
      $(apostrophe),$\
      $(apostrophe)$(backslash)$(apostrophe)$(apostrophe),$\
      $1))$\
  $(apostrophe)

# Appends $1 and $2,
# adding a space between them only if they're both nonempty.
space.2=$(if $1,$(if $2,$1$(space)$2,$1),$2)

# Shows the definition of a variable for Make.
var.1=$\
  $(let f,$(flavor $1),$\
  $(number-sign) $(origin $1)$(LF)$\
  $(if $(call equal.2,$f,undefined),$\
    undefine $1,$\
  $(else)$(if $(call equal.2,$f,recursive),$\
    $1=$(value $1),$\
  $(else)$(if $(call equal.2,$f,simple),$\
    $1:=$(value $1),$\
  $(else)$\
    $(error [$$(flavor $1)]=[$f]))))$(LF))

# Tells whether a variable is defined.
defined.1=$\
  $(call not.1,$(call equal.2,$(flavor $1),undefined))


# Commands
################################################################

CC:=cc

ECHO:=$\
  printf '%s' --

# HD=hexdump $(hexdump-flags)

HD=xxd $(xxd-flags)

DIFF=$\
  $(call space.2,$\
    colordiff $(diff-flags),$\
    $(call get.2,DIFFFLAGS,$(null)))

# DIFF=$\
#   $(call space.2,$\
#     git diff $(git-diff-flags),$\
#     $(call get.2,DIFFFLAGS,$(null)))

LINK=$\
  $(call space.2,$\
    $(CC),$\
    $(call get.2,LDFLAGS,$(null)))

NB=$\
  $(call space.2,$\
    ./nb,$\
    $(call get.2,NBFLAGS,$(null)))

OTOOL=$\
  $(call space.2,$\
    otool $(otool-flags),$\
    $(call get.2,OTOOLFLAGS,$(null)))


# Extra Flags
################################################################

#CFLAGS:=

# @var/CFLAGS:;-$(if $(call defined.1,CFLAGS),true,false)
# .PHONY:@var/CFLAGS
# .IGNORE:@var/CFLAGS

#DIFFFLAGS:=

#HDFLAGS:=

#LDFLAGS:=

#NBFLAGS:=

#OTOOLFLAGS:=


# Required Flags
################################################################

compile-flags=\
  $(compile-language-flags)\
  $(compile-profile-flags)\
  $(compile-warning-flags)

  compile-language-flags=\
    -std=c23

  compile-profile-flags=\
    -g

  compile-warning-flags=\
    $(compile-warning-enabled-flags)\
    $(compile-warning-error-flags)\
    $(compile-warning-disabled-flags)

    compile-warning-enabled-flags=\
      -Wall\
      -Wextra\
      -Wpedantic

    compile-warning-error-flags=\
      -Werror=format\
      -Werror=return-type

    compile-warning-disabled-flags=\
      -Wno-extra-semi\
      -Wno-overlength-strings

diff-flags:=\
  --expand-tabs\
  --side-by-side\
  --suppress-common-lines\
  --width=130

git-diff-flags:=\
  --anchored=\
  --diff-algorithm=minimal\
  --no-index\
  --unified=0

hexdump-flags=\
  $(hexdump-format-flag)

  hexdump-format-flag=\
    -e $(hexdump-format)

    hexdump-format=\
      $(let a,4/1 "%02X",$\
      $(let b," ",$\
      $(let c,"\n",$\
      $(call quote.1,$a $b $a $b $a $b $a $c))))

otool-flags=\
  $(otool-fat-headers-flag)\
  $(otool-archive-header-flag)\
  $(otool-mach-header-flag)\
  $(otool-load-commands-flag)\
  $(otool-shared-libraries-flag)\
  $(otool-shared-library-id-flag)\
  $(otool-all-text-sections-flag)\
  $(otool-data-section-flag)\
  $(otool-objective-c-flag)\
  $(otool-relocation-entries-flag)\
  $(otool-indirect-symbol-table-flag)\
  $(otool-data-in-code-flag)\
  $(otool-verbose-flag)\
  $(otool-verbose-disassembly-flag)\
  $(otool-llvm-disassembler-flag)\
  $(otool-opcode-bytes-flag)\
  $(otool-info-plist-flag)\
  $(otool-linker-hints-flag)

    otool-fat-headers-flag=-f
    otool-archive-header-flag=-a
    otool-mach-header-flag=-h
    otool-load-commands-flag=-l
    otool-shared-libraries-flag=-L
    otool-shared-library-id-flag=-D
    otool-all-text-sections-flag=-x
    otool-data-section-flag=-d
    otool-objective-c-flag=-o
    otool-relocation-entries-flag=-r
    otool-indirect-symbol-table-flag=-I
    otool-data-in-code-flag=-G
    otool-verbose-flag=-v
    otool-verbose-disassembly-flag=-V
    otool-llvm-disassembler-flag=-q
    otool-opcode-bytes-flag=-j
    otool-info-plist-flag=-P
    otool-linker-hints-flag=-C

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
    $(call get.2,CFLAGS,$(null)))

diff-them=\
  $(DIFF)\
    $(first-prerequisite)\
    $(second-prerequisite)

hexdump-it=\
  $(call space.2,$\
    $(HD)\
      $(first-prerequisite)\
      >$(target),$\
    $(call get.2,HDFLAGS,$(null)))

link-them=\
  $(LINK)\
    $(prerequisite-bag)\
    -o $(target)

nb=\
  $(NB) $(target)

otool-it=\
  $(call space.2,$\
    $(OTOOL)\
      $(first-prerequisite)\
      >$(target),$\
    $(call get.2,OTOOLFLAGS,$(null)))


# Rules
################################################################

.PHONY:@default
@default:@all

  .PHONY:@build
  @all:@build
  @build:nb

    nb:\
      nb.o\
      ;$(link-them)

      nb.o:\
        nb.c\
        ;$(compile-it)

  .PHONY:@test
  @all:@test
  @test:@test/reow

    .PHONY:@test/reow
    @test/reow:\
      @test/reow/hex\
      @test/reow/otool

      .PHONY:@test/reow/hex
      @test/reow/hex:\
        want/reow.hex\
        have/reow.hex\
        ;$(diff-them)

        want/reow.hex:\
          want/reow.bin\
          ;$(hexdump-it)

          want/reow.bin:\
            reow.o\
            |@dir/want\
            ;$(link-them)

        have/reow.hex:\
          have/reow.bin\
          ;$(hexdump-it)

          have/reow.bin:\
            nb\
            |@dir/have\
            ;$(nb)

        reow.o:compile-flags:=
        reow.o:\
          reow.c\
          ;$(compile-it)

      .PHONY:@test/reow/otool
      @test/reow/otool:\
        DIFFFLAGS=\
          --ignore-matching-lines=$\
            $(call quote.1,^(want|have)/reow\.bin:$)
      @test/reow/otool:\
        want/reow.otool\
        have/reow.otool\
        ;$(diff-them)

        want/reow.otool:\
          want/reow.bin\
          ;$(otool-it)

        have/reow.otool:\
          have/reow.bin\
          ;$(otool-it)


# Special Rules
################################################################

# A force target, allowing phony pattern rules.
@phony:;

# Marks all @-prefixed targets as phony if not otherwise marked.
@%:@phony

# Allows depending on whether a directory exists.
@dir/%:@phony
;[[ -d $(call quote.1,$(stem)) ]] || \
;  mkdir $(call quote.1,$(stem))

# # Allows depending on whether a variable is set.
# @var/%:@phony
# ;$(info $(call var.1,$(stem)))$\
# ;$(ECHO) $(call quote.1,$(call var.1,$(stem)))
# ;$(if $(call defined.1,$(stem)),true,false)

# # Allows depending on the value of a variable
# # by recording its definition in a file.
# ;$(let old,$(file <var/$(stem),$\
# ;$(let new,$(call get.2,$(stem),$(null)),$\
# ;  $(if $(call not.1,$(call equal.2,$(old),$(new))),$\
# ;    $(file >var/$(stem),$(new))))))
#
# ; [[ -f $(target) ]] $(call var.1,$(stem))

# Marks all makefiles as not needing to be rebuilt.
$(MAKEFILE_LIST)::;

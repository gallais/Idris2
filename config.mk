##### Options which a user might set before building go here #####

# Where to install idris2 binaries and libraries (must be an absolute path)
PREFIX ?= $(HOME)/.idris2

CHEZ ?= chez-scheme

# Racket's compiler called raco.
RACKET_RACO ?= raco

# Default code generator, aka CG. This is passed to the libraries for
# incremental builds, but overridable via environment variables or
# arguments to make: make IDRIS2_CG=racket
IDRIS2_CG ?= chez

# In the normal workflow you don't need to set this, but if you want
# to use an external Idris executable to be used as stage 0, then you
# can provide it here.
#BOOTSTRAP_IDRIS=

# For Windows targets. Set to 1 to support Windows 7.
OLD_WIN ?= 0

# When set to anything non-empty, it enables debug output from the makefile.
DEBUG_IDRIS_BUILD_SYSTEM ?=

##################################################################

# Make sure it's an absolute path, because it will be inserted into #!
# shell headers. The 'override' is needed for the case when it's
# specified as `make CHEZ=foo bootstrap`, e.g. as in the nix build.
override CHEZ := $(shell which $(CHEZ) 2>/dev/null)

# Idris 2 executable we're building
NAME = idris2

RANLIB ?= ranlib
AR ?= ar

CFLAGS := -Wall $(CFLAGS)
LDFLAGS := $(LDFLAGS)

empty :=
space := $(empty) $(empty)

EXE_SUFFIX :=
SHLIB_SUFFIX := .so

MACHINE := $(shell $(CC) -dumpmachine)
ifneq (,$(findstring cygwin, $(MACHINE)))
	OS := windows
	SHLIB_SUFFIX := .dll
	EXE_SUFFIX := .exe
else ifneq (,$(findstring mingw, $(MACHINE)))
	OS := windows
	SHLIB_SUFFIX := .dll
	EXE_SUFFIX := .exe
else ifneq (,$(findstring windows, $(MACHINE)))
	OS := windows
	SHLIB_SUFFIX := .dll
	EXE_SUFFIX := .exe
else ifneq (,$(findstring darwin, $(MACHINE)))
	OS := darwin
	SHLIB_SUFFIX := .dylib
else ifneq (, $(findstring bsd, $(MACHINE)))
	OS := bsd
else
	OS := linux
endif

ifneq ($(OS),windows)
	CFLAGS += -fPIC
else ifneq (, $(findstring NT-6.1,$(shell uname)))
	OLD_WIN = 1
endif

ifeq ($(OS),windows)
  # This produces D:/../.. style paths
  IDRIS2_PREFIX := $(shell cygpath -m ${PREFIX})
  IDRIS2_CURDIR := $(shell cygpath -m ${CURDIR})
  SEP := ;
else
  IDRIS2_PREFIX := ${PREFIX}
  IDRIS2_CURDIR := ${CURDIR}
  SEP := :
endif

export OS OLD_WIN

ifeq ($(IDRIS2_CG),chez)
  ifeq (,$(shell which "$(CHEZ)"))
    $(warning The CHEZ variable should point to a working Chez Scheme executable.)
  endif
else ifeq ($(IDRIS2_CG),racket)
  ifeq (,$(shell which "$(RACKET_RACO)"))
    $(warning The RACKET_RACO variable should point to a working raco executable of Racket.)
  endif
endif

ifneq ($(DEBUG_IDRIS_BUILD_SYSTEM),)
  $(info OS is [$(OS)], SHLIB_SUFFIX is [$(SHLIB_SUFFIX)], OLD_WIN is [$(OLD_WIN)], CHEZ is [$(CHEZ)], RACKET_RACO is [$(RACKET_RACO)], IDRIS2_CG is [$(IDRIS2_CG)], PREFIX is [$(PREFIX)].)
endif

# Add a custom.mk file to override any of the configurations
-include custom.mk

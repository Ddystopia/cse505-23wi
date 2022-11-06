# This Makefile uses the CSE course web directories to deploy our notes.
#
# Simply run `make` to deploy the website.
#
# If your CSE netid is different than your local username, you should set the
# USER variable on the command line. For example, if your CSE netid was abc123,
# you would run
#
#    make USER=abc123

SHELL = /bin/bash

PUBLIC_DIR = /cse/web/courses/cse505/23wi/notes

LOGIN = $(USER)
MACHINE = attu

# -L replaces any symbolic links with their referred files
# -chown=:cse505 forces the files on the recieving side to be owned by the cse505 group
# --chmod=D2775,F664 forces all files on receiving end to have the following permissions:
#      Owner:  RW-  (files)   RWX         (directories)
#      Group:  RW-  (files)   RWX+setgid  (directories)
#      Others: R--  (files)   R-X         (directories)
COMMON_RSYNC_OPTS = -vlzrptO --exclude ".*"
OUTGOING_RSYNC_OPTS = $(COMMON_RSYNC_OPTS) --chown=:cse505 --chmod=D2775,F664

.PHONY: all
all: public

.PHONY: build
build:
	zola build

.PHONY: public
public: build check-rsync-version
	@echo 'cd public && rsync . ${LOGIN}@${MACHINE}.cs.washington.edu:${PUBLIC_DIR}'
	@cd public && rsync ${OUTGOING_RSYNC_OPTS} . ${LOGIN}@${MACHINE}.cs.washington.edu:${PUBLIC_DIR} || echo ''

.PHONY: check-rsync-version
check-rsync-version:
	@rsync --version | grep '^rsync *version' | sed 's/rsync *version \([^ ]*\).*/\1/' | grep -q ^3 || (echo 'your version of rsync is too old. if you are on a mac, run "brew install rsync" and then rerun this Makefile'; exit 1)

HW_NUM=1
HW_DIR="hw$(HW_NUM)"
HW_ZIP=hw$(HW_NUM).zip

HW_FILES= \
	$(HW_DIR)/HW$(HW_NUM).v

COQC=coqc -q

ifdef OS
# rm is aliased to powershell Remove-item, use .exe to not use alias,
# which is link to busybox
DEL=rm.exe
else
DEL=rm
endif

.PHONY: coq
coq:
	$(COQC) HW$(HW_NUM).v

.PHONY: grade
grade: sig admit

.PHONY: sig
sig: coq
	# check that everything has expected type
	@$(COQC) HW$(HW_NUM)sig.v \
		&& echo "looks good. everything typechecked." \
		|| { echo "WARNING: something from the starter code was edited!!"; \
		     exit 1; }


.PHONY: admit
admit: HW$(HW_NUM).v
	# check for admits
	@cat HW$(HW_NUM).v \
		| egrep -n -C 2 'dmit' \
		&& echo "WARNING: your solution still has admits!!!" \
		|| echo "looks good. no admits found."

.PHONY: clean
clean:
	$(DEL) -rf *.vo *.glob .*.aux .*.cache *.vos *.vok

.PHONY: package
package:
	cd .. && $(DEL) -f $(HW_ZIP) && zip $(HW_ZIP) $(HW_FILES)

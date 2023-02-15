CURRENT_DIR=.
# COQBIN = D:/Coq8.12.2/Coq/bin/

-include CONFIGURE

COQC=$(COQBIN)coqc
COQDEP=$(COQBIN)coqdep

DIRS = \
  General Verif


COQ_FLAG = -Q $(CURRENT_DIR) RBT
DEP_FLAG = -Q $(CURRENT_DIR) RBT

# COQ_FLAG = -Q $(CURRENT_DIR) RBT -Q ~/Documents/vst-latest/VST-master/msl VST.msl -Q ~/Documents/vst-latest/VST-master/sepcomp VST.sepcomp -Q ~/Documents/vst-latest/VST-master/veric VST.veric -Q ~/Documents/vst-latest/VST-master/floyd VST.floyd -Q ~/Documents/vst-latest/VST-master/progs VST.progs -R ~/Documents/vst-latest/VST-master/compcert compcert
# DEP_FLAG = -Q $(CURRENT_DIR) RBT -Q ~/Documents/vst-latest/VST-master/msl VST.msl -Q ~/Documents/vst-latest/VST-master/sepcomp VST.sepcomp -Q ~/Documents/vst-latest/VST-master/veric VST.veric -Q ~/Documents/vst-latest/VST-master/floyd VST.floyd -Q ~/Documents/vst-latest/VST-master/progs VST.progs -R ~/Documents/vst-latest/VST-master/compcert compcert


General_FILES = \
  Basic.v BinaryTree.v BinarySearchTree.v

Verif_FILES = \
  RBtree_Type.v RBtree_Definition.v relation_map.v Half_Tree.v Abstract.v SegmentChange.v general_split.v lookup.v Insert.v Delete.v Delete_check.v rbt.v verif_rbt_toolbox.v


FILES = \
  $(General_FILES:%.v=General/%.v) \
  $(Verif_FILES:%.v=Verif/%.v)

$(FILES:%.v=%.vo): %.vo: %.v
	@echo COQC $*.v
	@$(COQC) $(COQ_FLAG) $(CURRENT_DIR)/$*.v

all: \
  $(FILES:%.v=%.vo)

depend:
	$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

.depend:
	@$(COQDEP) $(DEP_FLAG) $(FILES) > .depend

clean:
	@rm */*.vo */*.glob

.DEFAULT_GOAL := all

include .depend


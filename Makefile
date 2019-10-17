PWD := $(shell pwd)
RUN = $(PWD)/run

SVA_TEST ?= 00_counter

SIM_F = $(PWD)/out
VSIM_BIN = cd $(SIM_F) && vsim

VSIM_ARGS = -do $(RUN)/$(SVA_TEST).tcl

VSIM_F_CMD = -c
VSIM_F_CMD += -onfinish exit

VSIM_F_GUI = -gui

sim_clean:
	rm -rfd out

sim_dir: sim_clean
	mkdir -p out

sim_cmd: sim_dir
	$(VSIM_BIN) $(VSIM_ARGS) $(VSIM_F_CMD)

sim_gui: sim_dir
	$(VSIM_BIN) $(VSIM_ARGS) $(VSIM_F_GUI)

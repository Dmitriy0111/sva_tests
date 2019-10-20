help:
	$(info make sim_clean		-- delete simulation folder(out))
	$(info make sim_gui 		-- simulate example with modelsim in gui mode)
	$(info make sim_cmd 		-- simulate example with modelsim in cmd mode)
	$(info make sim 			-- the same as sim_gui)
	$(info)
	$(info Open and read Makefile for details)
	@true

PWD := $(shell pwd)
RUN = $(PWD)/run

SVA_TESTS = 00_counter 01_counter_en 02_counter_inc_dec

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

sim: sim_gui

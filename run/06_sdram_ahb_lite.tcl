
# compile rtl
vlog -sv ../06_sdram_ahb_lite/ahb_lite_sdram/src/ahb_lite_sdram/*.*v
# compile sdram model
vlog -sv ../06_sdram_ahb_lite/ahb_lite_sdram/src/testbench/sdr_sdram/*.*v +define+den512Mb +define+sg75 +define+x16 +define+SIMULATION
# compile interfaces
vlog -sv ../06_sdram_ahb_lite/my_testbench/interfaces/*.*v
# compile package
vlog -sv ../06_sdram_ahb_lite/my_testbench/test_pkg.*v
# compile testbench
vlog -sv ../06_sdram_ahb_lite/my_testbench/*_tb.*v

vsim -novopt work.sdram_ahb_lite_tb

run -all

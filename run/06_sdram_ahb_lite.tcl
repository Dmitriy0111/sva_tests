
# compile rtl
vlog -sv ../06_sdram_ahb_lite/ahb_lite_sdram/src/ahb_lite_sdram/*.*v
# compile sdram model
vlog -sv ../06_sdram_ahb_lite/ahb_lite_sdram/src/testbench/sdr_sdram/*.*v +define+den128Mb +define+sg75 +define+x16 +define+SIMULATION
# compile interfaces
vlog -sv ../06_sdram_ahb_lite/my_testbench/interfaces/*.*v
# compile package
vlog -sv ../06_sdram_ahb_lite/my_testbench/test_pkg.*v
# compile testbench
vlog -sv ../06_sdram_ahb_lite/my_testbench/*_tb.*v

vsim -novopt work.sdram_ahb_lite_tb +TEST=DIRECT_TEST

run 0

mem save -o bank0_init.mem -f hex /sdram_ahb_lite_tb/sdram0/Bank0
mem save -o bank1_init.mem -f hex /sdram_ahb_lite_tb/sdram0/Bank1
mem save -o bank2_init.mem -f hex /sdram_ahb_lite_tb/sdram0/Bank2
mem save -o bank3_init.mem -f hex /sdram_ahb_lite_tb/sdram0/Bank3

add wave -divider "DUT signals"
add wave -position insertpoint sim:/sdram_ahb_lite_tb/ahb_lite_sdram_0/*
add wave -divider "AHB lite assertions"
add wave /sdram_ahb_lite_tb/ahb_lite_if_0/haddr_unk_a
add wave /sdram_ahb_lite_tb/ahb_lite_if_0/haddr_unk_c

add wave /sdram_ahb_lite_tb/ahb_lite_if_0/hburst_unk_a
add wave /sdram_ahb_lite_tb/ahb_lite_if_0/hburst_unk_c

add wave /sdram_ahb_lite_tb/ahb_lite_if_0/hsize_unk_a
add wave /sdram_ahb_lite_tb/ahb_lite_if_0/hsize_unk_c

add wave /sdram_ahb_lite_tb/ahb_lite_if_0/hmastlock_unk_a
add wave /sdram_ahb_lite_tb/ahb_lite_if_0/hmastlock_unk_c

add wave /sdram_ahb_lite_tb/ahb_lite_if_0/hprot_unk_a
add wave /sdram_ahb_lite_tb/ahb_lite_if_0/hprot_unk_c

add wave /sdram_ahb_lite_tb/ahb_lite_if_0/htrans_unk_a
add wave /sdram_ahb_lite_tb/ahb_lite_if_0/htrans_unk_c

add wave /sdram_ahb_lite_tb/ahb_lite_if_0/hresp_unk_a
add wave /sdram_ahb_lite_tb/ahb_lite_if_0/hresp_unk_c

run -all

mem save -o bank0.mem -f hex /sdram_ahb_lite_tb/sdram0/Bank0
mem save -o bank1.mem -f hex /sdram_ahb_lite_tb/sdram0/Bank1
mem save -o bank2.mem -f hex /sdram_ahb_lite_tb/sdram0/Bank2
mem save -o bank3.mem -f hex /sdram_ahb_lite_tb/sdram0/Bank3

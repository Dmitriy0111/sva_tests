
# compile sources
vlog -sv ../00_counter/*.*v

vsim -novopt work.counter_tb

add wave -divider "DUT signals"
add wave /counter_tb/counter_dut/*
add wave -divider "DUT assertions"
add wave /counter_tb/counter_dut/inc_a
add wave /counter_tb/counter_dut/inc_c
add wave /counter_tb/counter_dut/unk_a
add wave /counter_tb/counter_dut/unk_c

run -all

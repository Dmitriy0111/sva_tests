
# compile sources
vlog -sv ../01_counter_en/*.*v

vsim -novopt work.counter_en_tb

add wave -divider "DUT signals"
add wave -position insertpoint sim:/counter_en_tb/*
add wave -divider "DUT assertions"
add wave /counter_en_tb/counter_en_dut/inc_a
add wave /counter_en_tb/counter_en_dut/inc_c
add wave /counter_en_tb/counter_en_dut/unk_a
add wave /counter_en_tb/counter_en_dut/unk_c

run -all

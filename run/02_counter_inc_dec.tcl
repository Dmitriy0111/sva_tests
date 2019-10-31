
# compile sources
vlog -sv ../02_counter_inc_dec/*.*v

vsim -novopt work.counter_inc_dec_tb

add wave -divider "DUT signals"
add wave /counter_inc_dec_tb/counter_inc_dec_dut/*
add wave -divider "DUT assertions"
add wave /counter_inc_dec_tb/counter_inc_dec_dut/inc_a
add wave /counter_inc_dec_tb/counter_inc_dec_dut/inc_c
add wave /counter_inc_dec_tb/counter_inc_dec_dut/dec_a
add wave /counter_inc_dec_tb/counter_inc_dec_dut/dec_c
add wave /counter_inc_dec_tb/counter_inc_dec_dut/unk_a
add wave /counter_inc_dec_tb/counter_inc_dec_dut/unk_c
add wave /counter_inc_dec_tb/counter_inc_dec_dut/hold_a
add wave /counter_inc_dec_tb/counter_inc_dec_dut/hold_c
add wave -divider "DUT assertion unit"
add wave /counter_inc_dec_tb/counter_au_0/inc_a 
add wave /counter_inc_dec_tb/counter_au_0/inc_c 
add wave /counter_inc_dec_tb/counter_au_0/dec_a 
add wave /counter_inc_dec_tb/counter_au_0/dec_c 
add wave /counter_inc_dec_tb/counter_au_0/unk_a
add wave /counter_inc_dec_tb/counter_au_0/unk_c
add wave /counter_inc_dec_tb/counter_au_0/hold_a
add wave /counter_inc_dec_tb/counter_au_0/hold_c

run -all

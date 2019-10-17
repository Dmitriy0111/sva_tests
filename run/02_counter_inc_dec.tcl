
# compile sources
vlog -sv ../02_counter_inc_dec/*.*v

vsim -novopt work.counter_inc_dec_tb

add wave /counter_inc_dec_tb/counter_inc_dec_dut/inc_dec_a

run -all

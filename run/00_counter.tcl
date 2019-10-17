
# compile sources
vlog -sv ../00_counter/*.*v

vsim -novopt work.counter_tb

add wave /counter_tb/counter_dut/inc_a

run -all

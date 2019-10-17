
# compile sources
vlog -sv ../01_counter_en/*.*v

vsim -novopt work.counter_en_tb

add wave /counter_en_tb/counter_en_dut/inc_a

run -all

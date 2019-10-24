vlib work
# compile rtl
vlog -sv ../05_simple_spi_wb/simple_spi/rtl/verilog/*.*v
# compile testbench and other files
vlog -sv ../05_simple_spi_wb/my_testbench/*.*v

vsim -novopt work.simple_spi_tb

add wave -divider "DUT signals"
add wave /simple_spi_tb/simple_spi_dut/*
add wave -divider "DUT assertions"
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_spcr_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_spcr_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_sper_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_sper_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_ss_r_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_ss_r_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/test_out_spcr_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/test_out_spcr_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/test_out_spsr_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/test_out_spsr_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/test_out_sper_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/test_out_sper_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/test_out_ss_r_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/test_out_ss_r_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/test_out_rfdout_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/test_out_rfdout_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/test_out_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/test_out_c

run -all

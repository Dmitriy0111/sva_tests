
# compile rtl
vlog -sv ../05_simple_spi_wb/simple_spi/rtl/verilog/*.*v
# compile testbench and other files
vlog -sv ../05_simple_spi_wb/my_testbench/*.*v
vlog -sv ../05_simple_spi_wb/my_testbench/classes/*.*v

vsim -novopt work.simple_spi_tb -assertdebug

add wave -divider "DUT signals"
add wave /simple_spi_tb/simple_spi_dut/*
add wave -divider "DUT assertions"
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_spcr_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_spcr_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_sper_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_sper_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_ss_r_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_ss_r_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_spif_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_spif_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_wcol_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_wcol_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_state_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_state_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_bcnt_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_bcnt_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_treg_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_treg_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_wfre_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_wfre_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_rfwe_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_rfwe_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_sck_o_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/rst_sck_o_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/test_clock_div_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/test_clock_div_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/idle2clk_ph2_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/idle2clk_ph2_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/clk_ph2_2clk_ph1_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/clk_ph2_2clk_ph1_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/clk_ph1_2idle_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/clk_ph1_2idle_c

add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/clk_ph1_2clk_ph2_a
add wave /simple_spi_tb/simple_spi_dut/simple_spi_pm_0/clk_ph1_2clk_ph2_c

add wave -divider "Interface assertions"
add wave /simple_spi_tb/wb_if_/unk_data_wr_a
add wave /simple_spi_tb/wb_if_/unk_data_wr_c

add wave /simple_spi_tb/wb_if_/unk_addr_wr_a
add wave /simple_spi_tb/wb_if_/unk_addr_wr_c

run -all

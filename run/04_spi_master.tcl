
# compile sources
vlog -sv ../04_spi_master/*.*v

vsim -novopt work.spi_master_tb

add wave -divider "DUT signals"
add wave /spi_master_tb/spi_master_dut/*
add wave -divider "DUT assertions"
add wave /spi_master_tb/spi_master_dut/rst_data_int_a
add wave /spi_master_tb/spi_master_dut/rst_data_int_c

add wave /spi_master_tb/spi_master_dut/rst_cpol_int_a
add wave /spi_master_tb/spi_master_dut/rst_cpol_int_c

add wave /spi_master_tb/spi_master_dut/rst_cpha_int_a
add wave /spi_master_tb/spi_master_dut/rst_cpha_int_c

add wave /spi_master_tb/spi_master_dut/rst_comp_int_a
add wave /spi_master_tb/spi_master_dut/rst_comp_int_c

add wave /spi_master_tb/spi_master_dut/rst_comp_c_a
add wave /spi_master_tb/spi_master_dut/rst_comp_c_c

add wave /spi_master_tb/spi_master_dut/rst_bit_c_a
add wave /spi_master_tb/spi_master_dut/rst_bit_c_c

add wave /spi_master_tb/spi_master_dut/rst_tx_req_ack_a
add wave /spi_master_tb/spi_master_dut/rst_tx_req_ack_c

add wave /spi_master_tb/spi_master_dut/rst_sck_int_a
add wave /spi_master_tb/spi_master_dut/rst_sck_int_c

add wave /spi_master_tb/spi_master_dut/rst_cs_a
add wave /spi_master_tb/spi_master_dut/rst_cs_c

add wave /spi_master_tb/spi_master_dut/rst_sdo_a
add wave /spi_master_tb/spi_master_dut/rst_sdo_c

add wave /spi_master_tb/spi_master_dut/rst_msb_lsb_int_a
add wave /spi_master_tb/spi_master_dut/rst_msb_lsb_int_c

add wave /spi_master_tb/spi_master_dut/unk_data_int_a
add wave /spi_master_tb/spi_master_dut/unk_data_int_c

add wave /spi_master_tb/spi_master_dut/unk_cpol_int_a
add wave /spi_master_tb/spi_master_dut/unk_cpol_int_c

add wave /spi_master_tb/spi_master_dut/unk_cpha_int_a
add wave /spi_master_tb/spi_master_dut/unk_cpha_int_c

add wave /spi_master_tb/spi_master_dut/unk_comp_int_a
add wave /spi_master_tb/spi_master_dut/unk_comp_int_c

add wave /spi_master_tb/spi_master_dut/idle_change_a
add wave /spi_master_tb/spi_master_dut/idle_change_c

add wave /spi_master_tb/spi_master_dut/transmit_change_a
add wave /spi_master_tb/spi_master_dut/transmit_change_c

add wave /spi_master_tb/spi_master_dut/post_tr_change_a
add wave /spi_master_tb/spi_master_dut/post_tr_change_c

add wave /spi_master_tb/spi_master_dut/wait_change_a
add wave /spi_master_tb/spi_master_dut/wait_change_c

run -all

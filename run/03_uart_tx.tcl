
# compile sources
vlog -sv ../03_uart_tx/*.*v

vsim -novopt work.uart_transmitter_tb

add wave -divider "DUT signals"
add wave /uart_transmitter_tb/uart_transmitter_dut/*
add wave -divider "DUT assertions"
add wave /uart_transmitter_tb/uart_transmitter_dut/idle2start_a
add wave /uart_transmitter_tb/uart_transmitter_dut/idle2start_c
add wave /uart_transmitter_tb/uart_transmitter_dut/idle_change_a
add wave /uart_transmitter_tb/uart_transmitter_dut/idle_change_c

add wave /uart_transmitter_tb/uart_transmitter_dut/start2tr_a
add wave /uart_transmitter_tb/uart_transmitter_dut/start2tr_c
add wave /uart_transmitter_tb/uart_transmitter_dut/start_change_a
add wave /uart_transmitter_tb/uart_transmitter_dut/start_change_c

add wave /uart_transmitter_tb/uart_transmitter_dut/tr2stop_a
add wave /uart_transmitter_tb/uart_transmitter_dut/tr2stop_c
add wave /uart_transmitter_tb/uart_transmitter_dut/tr_change_a
add wave /uart_transmitter_tb/uart_transmitter_dut/tr_change_c

add wave /uart_transmitter_tb/uart_transmitter_dut/stop2wait_a
add wave /uart_transmitter_tb/uart_transmitter_dut/stop2wait_c
add wave /uart_transmitter_tb/uart_transmitter_dut/stop_change_a
add wave /uart_transmitter_tb/uart_transmitter_dut/stop_change_c

add wave /uart_transmitter_tb/uart_transmitter_dut/wait2idle_a
add wave /uart_transmitter_tb/uart_transmitter_dut/wait2idle_c
add wave /uart_transmitter_tb/uart_transmitter_dut/wait_change_a
add wave /uart_transmitter_tb/uart_transmitter_dut/wait_change_c

add wave /uart_transmitter_tb/uart_transmitter_dut/unk_tx_data_int_a
add wave /uart_transmitter_tb/uart_transmitter_dut/unk_tx_data_int_c

add wave /uart_transmitter_tb/uart_transmitter_dut/unk_comp_int_a
add wave /uart_transmitter_tb/uart_transmitter_dut/unk_comp_int_c

add wave /uart_transmitter_tb/uart_transmitter_dut/unk_stop_sel_int_a
add wave /uart_transmitter_tb/uart_transmitter_dut/unk_stop_sel_int_c

add wave /uart_transmitter_tb/uart_transmitter_dut/req_ack_a
add wave /uart_transmitter_tb/uart_transmitter_dut/req_ack_c

add wave /uart_transmitter_tb/uart_transmitter_dut/rst_tx_data_int_a
add wave /uart_transmitter_tb/uart_transmitter_dut/rst_tx_data_int_c

add wave /uart_transmitter_tb/uart_transmitter_dut/rst_stop_sel_int_a
add wave /uart_transmitter_tb/uart_transmitter_dut/rst_stop_sel_int_c

add wave /uart_transmitter_tb/uart_transmitter_dut/rst_comp_c_a
add wave /uart_transmitter_tb/uart_transmitter_dut/rst_comp_c_c

add wave /uart_transmitter_tb/uart_transmitter_dut/rst_bit_c_a
add wave /uart_transmitter_tb/uart_transmitter_dut/rst_bit_c_c

add wave /uart_transmitter_tb/uart_transmitter_dut/rst_tx_req_ack_a
add wave /uart_transmitter_tb/uart_transmitter_dut/rst_tx_req_ack_c

add wave /uart_transmitter_tb/uart_transmitter_dut/rst_uart_tx_a
add wave /uart_transmitter_tb/uart_transmitter_dut/rst_uart_tx_c

add wave /uart_transmitter_tb/uart_transmitter_dut/rst_comp_int_a
add wave /uart_transmitter_tb/uart_transmitter_dut/rst_comp_int_c

run -all

/*
*  File            :   simple_spi_tb.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.22
*  Language        :   SystemVerilog
*  Description     :   This is spi master testbench
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`include "classes/wb_driver.sv"

module simple_spi_tb();

    parameter           T = 10,
                        repeat_n = 100,
                        rst_delay = 7,
                        start_delay = 200;

    parameter           SS_WIDTH = 1;

    /// 8bit WISHBONE bus slave interface
    logic   [0          : 0]    clk_i;      // clock
    logic   [0          : 0]    rst_i;      // reset (synchronous active high)
    logic   [0          : 0]    inta_o;     // interrupt output
    // SPI port
    logic   [0          : 0]    sck_o;      // serial clock output
    logic   [SS_WIDTH-1 : 0]    ss_o;       // slave select (active low)
    logic   [0          : 0]    mosi_o;     // MasterOut SlaveIN
    logic   [0          : 0]    miso_i;     // MasterIn SlaveOut

    logic   [7 : 0]     r_data_wb;

    wb_if       
    wb_if_
    ( 
        .CLK        ( clk_i         ),
        .RST        ( rst_i         )
    );

    simple_spi 
    #(
        .SS_WIDTH   ( SS_WIDTH      )
    )
    simple_spi_dut
    (
        // 8bit WISHBONE bus slave interface
        .clk_i      ( clk_i         ),      // clock
        .rst_i      ( rst_i         ),      // reset (synchronous active high)
        .cyc_i      ( wb_if_.CYC    ),      // cycle
        .stb_i      ( wb_if_.STB    ),      // strobe
        .adr_i      ( wb_if_.ADR    ),      // address
        .we_i       ( wb_if_.WE     ),      // write enable
        .dat_i      ( wb_if_.DATA_O ),      // data input
        .dat_o      ( wb_if_.DATA_I ),      // data output
        .ack_o      ( wb_if_.ACK    ),      // normal bus termination
        .inta_o     ( inta_o        ),      // interrupt output
        // SPI port
        .sck_o      ( sck_o         ),      // serial clock output
        .ss_o       ( ss_o          ),      // slave select (active low)
        .mosi_o     ( mosi_o        ),      // MasterOut SlaveIN
        .miso_i     ( miso_i        )       // MasterIn SlaveOut
    );

    bind simple_spi_dut
    simple_spi_pm
    #(
        .SS_WIDTH   ( SS_WIDTH      )
    )
    simple_spi_pm_0
    (
        .*
    );

    wb_driver   wb_driver_0 = new(wb_if_);

    initial
    begin
        #(start_delay);
        clk_i = '1;
        forever
            #(T/2)  clk_i = !clk_i;
    end
    initial
    begin
        #(start_delay);
        $info("Start test reset regs");
        rst_i = '1;
        repeat(rst_delay) @(posedge clk_i);
        rst_i = '0;
        $info("Stop test reset regs");
    end
    initial
    begin
        #(start_delay);
        wb_driver_0.reset_signals();
        miso_i = '0;
        @(negedge rst_i);
        $info("Start test dat_o");
        repeat(repeat_n)
        begin
            wb_driver_0.set_adr($urandom_range(0,7));
            @(posedge clk_i);
        end
        $info("Stop test dat_o");
        repeat(20)
        begin
            wb_driver_0.write_data(3'b000,8'b01011000);
            wb_driver_0.write_data(3'b011,8'b00000010);
            wb_driver_0.write_data(3'b010,$urandom_range(0,255));
            do
            begin
                wb_driver_0.read_data(3'b001,r_data_wb);
            end
            while( ( r_data_wb & 8'h80 ) == 0 );
            wb_driver_0.write_data(3'b001, r_data_wb );
        end
        repeat (200) @(posedge clk_i);
        $stop;
    end
    
endmodule : simple_spi_tb

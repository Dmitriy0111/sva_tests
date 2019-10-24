/*
*  File            :   simple_spi_tb.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.22
*  Language        :   SystemVerilog
*  Description     :   This is spi master testbench
*  Copyright(c)    :   2019 Vlasov D.V.
*/

module simple_spi_tb();

    parameter           T = 10,
                        repeat_n = 100,
                        rst_delay = 7,
                        start_delay = 200;

    parameter           SS_WIDTH = 1;

    /// 8bit WISHBONE bus slave interface
    logic   [0          : 0]    clk_i;      // clock
    logic   [0          : 0]    rst_i;      // reset (synchronous active high)
    logic   [0          : 0]    cyc_i;      // cycle
    logic   [0          : 0]    stb_i;      // strobe
    logic   [2          : 0]    adr_i;      // address
    logic   [0          : 0]    we_i;       // write enable
    logic   [7          : 0]    dat_i;      // data input
    logic   [7          : 0]    dat_o;      // data output
    logic   [0          : 0]    ack_o;      // normal bus termination
    logic   [0          : 0]    inta_o;     // interrupt output
    // SPI port
    logic   [0          : 0]    sck_o;      // serial clock output
    logic   [SS_WIDTH-1 : 0]    ss_o;       // slave select (active low)
    logic   [0          : 0]    mosi_o;     // MasterOut SlaveIN
    logic   [0          : 0]    miso_i;     // MasterIn SlaveOut

    simple_spi 
    #(
        .SS_WIDTH   ( SS_WIDTH      )
    )
    simple_spi_dut
    (
        // 8bit WISHBONE bus slave interface
        .clk_i      ( clk_i         ),      // clock
        .rst_i      ( rst_i         ),      // reset (synchronous active high)
        .cyc_i      ( cyc_i         ),      // cycle
        .stb_i      ( stb_i         ),      // strobe
        .adr_i      ( adr_i         ),      // address
        .we_i       ( we_i          ),      // write enable
        .dat_i      ( dat_i         ),      // data input
        .dat_o      ( dat_o         ),      // data output
        .ack_o      ( ack_o         ),      // normal bus termination
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
        rst_i = '1;
        repeat(rst_delay) @(posedge clk_i);
        rst_i = '0;
    end
    initial
    begin
        #(start_delay);
        cyc_i = '0;
        stb_i = '0;
        adr_i = 3'b100;
        we_i = '0;
        dat_i = '0;
        miso_i = '0;
        @(negedge rst_i);
        repeat(repeat_n)
        begin
            adr_i = $urandom_range(0,7);
            @(posedge clk_i);
        end
        $stop;
    end
    
endmodule : simple_spi_tb

/*
*  File            :   simple_spi_tb.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.22
*  Language        :   SystemVerilog
*  Description     :   This is spi master testbench
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`include "classes/wb_driver.sv"
`include "classes/spi_simple_cover.sv"
`include "classes/wb_random_gen.sv"
`include "classes/spi_monitor.sv"

module simple_spi_tb();

    parameter           T = 10,
                        repeat_n = 100,
                        rst_delay = 7,
                        start_delay = 200;

    parameter           SS_WIDTH = 8;

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
    bit     [0 : 0]     spi_ie;

    wb_if       
    wb_if_
    ( 
        .CLK        ( clk_i         ),
        .RST        ( rst_i         )
    );

    spi_if
    #(
        .slave_c    ( SS_WIDTH      )
    )
    spi_if_
    (
        .clk        ( clk_i         ),
        .rst        ( rst_i         )
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
        .sck_o      ( spi_if_.sck   ),      // serial clock output
        .ss_o       ( spi_if_.ss    ),      // slave select (active low)
        .mosi_o     ( spi_if_.mosi  ),      // MasterOut SlaveIN
        .miso_i     ( spi_if_.miso  )       // MasterIn SlaveOut
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

    wb_driver           wb_driver_0         = new( wb_if_   );
    spi_simple_cover    spi_simple_cover_0  = new( wb_if_   );
    wb_random_gen       wb_random_gen_0     = new(          );

    spi_monitor #( .ss_width( SS_WIDTH ) )  spi_monitor_[SS_WIDTH];

    initial
    begin
        spi_simple_cover_0.run();
    end

    genvar mon_i;
    generate
        for(mon_i=0 ; mon_i<SS_WIDTH ; mon_i++)
        begin : gen_mon
            initial
            begin
                spi_monitor_[mon_i] = new( spi_if_ , $psprintf("SPI_mon_%0d",mon_i) , mon_i );
                spi_monitor_[mon_i].run();
            end
        end
    endgenerate
    
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
        wb_random_gen_0.set_num_spi_slaves(SS_WIDTH);
        wb_driver_0.reset_signals();
        miso_i = '0;
        @(negedge rst_i);
        repeat(repeat_n)
        begin
            wb_random_gen_0.randomize();
            foreach(spi_monitor_[i])
            begin
                spi_monitor_[i].set_spi_mode(wb_random_gen_0.spi_mode);
                spi_monitor_[i].set_spi_clk_div(wb_random_gen_0.spi_clk_div);
            end
            spi_ie = wb_random_gen_0.spi_ie;
            wb_driver_0.write_data(3'b000, wb_random_gen_0.spcr    );
            wb_driver_0.write_data(3'b011, wb_random_gen_0.sper    );
            wb_driver_0.write_data(3'b100, wb_random_gen_0.ss_sel  );
            wb_driver_0.write_data(3'b010, wb_random_gen_0.tr_data );
            if( !spi_ie )
            do
            begin
                wb_driver_0.read_data(3'b001,r_data_wb);
            end
            while( ( r_data_wb & 8'h80 ) == 0 );
            else
                @(posedge inta_o);
            wb_driver_0.write_data(3'b100, '0 );
            wb_driver_0.write_data(3'b001, r_data_wb );
        end
        repeat (200) @(posedge clk_i);
        $stop;
    end
    
endmodule : simple_spi_tb

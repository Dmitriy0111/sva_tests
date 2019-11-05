/*
*  File            :   sdram_ahb_lite_tb.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.01
*  Language        :   SystemVerilog
*  Description     :   This is sdram ahb lite testbench
*  Copyright(c)    :   2019 Vlasov D.V.
*/

import test_pkg::*;

module sdram_ahb_lite_tb();

    timeunit        1ns;
    timeprecision   1ps;

    parameter       ADDR_BITS           = 12,       /* SDRAM Address input size */
                    ROW_BITS            = 12,       /* SDRAM Row address size */
                    COL_BITS            = 10,       /* SDRAM Column address size */
                    DQ_BITS             = 16,       /* SDRAM Data i/o size, only x16 supported */
                    DM_BITS             = 2,        /* SDRAM Data i/o mask size, only x2 supported */
                    BA_BITS             = 2,        /* SDRAM Bank address size */
                    SADDR_BITS          = (ROW_BITS + COL_BITS + BA_BITS);

    parameter       start_delay = 200,
                    repeat_c = 10000,
                    rst_delay = 7,
                    T = 20;

    logic   [0 : 0]     HCLK;
    logic   [0 : 0]     HRESETn;

    sock_data               write_sock_data;
    socket  #(sock_data)    write_sock = new(2);

    ahb_lite_if     
    ahb_lite_if_0
    (
        .HCLK       ( HCLK                      ),
        .HRESETn    ( HRESETn                   )
    );

    sdram_if
    #(
        .addr_bits  ( ADDR_BITS                 ),
        .ba_bits    ( BA_BITS                   ),
        .dq_bits    ( DQ_BITS                   ),
        .dm_bits    ( DM_BITS                   )
    )
    sdram_if_0();

    ahb_lite_sdram
    #(
        .ADDR_BITS  ( ADDR_BITS                 ),
        .ROW_BITS   ( ROW_BITS                  ),
        .COL_BITS   ( COL_BITS                  ),
        .DQ_BITS    ( DQ_BITS                   ),
        .DM_BITS    ( DM_BITS                   ),
        .BA_BITS    ( BA_BITS                   ),
        .SADDR_BITS ( SADDR_BITS                )
    )
    ahb_lite_sdram_0
    (
        //ABB-Lite side
        .HCLK       ( ahb_lite_if_0.HCLK        ),    
        .HRESETn    ( ahb_lite_if_0.HRESETn     ),
        .HADDR      ( ahb_lite_if_0.HADDR       ),
        .HBURST     ( ahb_lite_if_0.HBURST      ),
        .HMASTLOCK  ( ahb_lite_if_0.HMASTLOCK   ),
        .HPROT      ( ahb_lite_if_0.HPROT       ),
        .HSEL       ( ahb_lite_if_0.HSEL        ),
        .HSIZE      ( ahb_lite_if_0.HSIZE       ),
        .HTRANS     ( ahb_lite_if_0.HTRANS      ),
        .HWDATA     ( ahb_lite_if_0.HWDATA      ),
        .HWRITE     ( ahb_lite_if_0.HWRITE      ),
        .HREADY     ( ahb_lite_if_0.HREADY      ),
        .HRDATA     ( ahb_lite_if_0.HRDATA      ),
        .HREADYOUT  ( ahb_lite_if_0.HREADYOUT   ),
        .HRESP      ( ahb_lite_if_0.HRESP       ),
        .SI_Endian  ( '0                        ),

        .CKE        ( sdram_if_0.cke            ),
        .CSn        ( sdram_if_0.csn            ),
        .RASn       ( sdram_if_0.rasn           ),
        .CASn       ( sdram_if_0.casn           ),
        .WEn        ( sdram_if_0.wen            ),
        .ADDR       ( sdram_if_0.addr           ),
        .BA         ( sdram_if_0.ba             ),
        .DQ         ( sdram_if_0.dq             ),
        .DQM        ( sdram_if_0.dqm            )
    );

    sdr 
    sdram0 
    (
        .Clk        ( sdram_if_0.clk            ), 
        .Cke        ( sdram_if_0.cke            ), 
        .Cs_n       ( sdram_if_0.csn            ), 
        .Ras_n      ( sdram_if_0.rasn           ), 
        .Cas_n      ( sdram_if_0.casn           ), 
        .We_n       ( sdram_if_0.wen            ), 
        .Addr       ( sdram_if_0.addr           ), 
        .Ba         ( sdram_if_0.ba             ), 
        .Dq         ( sdram_if_0.dq             ), 
        .Dqm        ( sdram_if_0.dqm            )
    );

    ahb_driver
    ahb_driver_0 = new("AHB_DRIVER", ahb_lite_if_0);

    assign #(5) sdram_if_0.clk = HCLK;

    initial
    begin
        #(start_delay);
        HCLK = '0;
        forever
            #(T/2) HCLK = !HCLK;
    end

    initial
    begin
        #(start_delay);
        HRESETn = '0;
        repeat(rst_delay) @(posedge HCLK);
        HRESETn = '1;
    end

    initial
    begin
        @(posedge HRESETn);
        repeat(repeat_c) @(posedge HCLK);
        $stop;
    end

    initial
    begin
        @(posedge HRESETn);
        ahb_driver_0.reset_signals();
        ahb_driver_0.connect_write_sock(write_sock);
        repeat(200) @(posedge HCLK);
        ahb_driver_0.run();
    end

    initial
    begin
        @(posedge HRESETn);
        repeat(400) @(posedge HCLK);
        write_sock_data.addr = 32'h00000010;
        write_sock_data.data = 32'hAA5555AA;
        write_sock.send_msg(0, write_sock_data);
        write_sock.wait_side(1);
        write_sock_data.addr = 32'h00000014;
        write_sock_data.data = 32'h55AAAA55;
        write_sock.send_msg(0, write_sock_data);
        write_sock.wait_side(1);
        write_sock_data.addr = 32'h00000018;
        write_sock_data.data = 32'hFFFFFFFF;
        write_sock.send_msg(0, write_sock_data);
        write_sock.wait_side(1);
        write_sock_data.addr = 32'h0000001C;
        write_sock_data.data = 32'hEEEE7777;
        write_sock.send_msg(0, write_sock_data);
        write_sock.wait_side(1);
    end

endmodule : sdram_ahb_lite_tb
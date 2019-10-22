/*
*  File            :   spi_master_tb.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.22
*  Language        :   SystemVerilog
*  Description     :   This is spi master testbench
*  Copyright(c)    :   2019 Vlasov D.V.
*/

module spi_master_tb();

    parameter           T = 10,
                        repeat_n = 100,
                        rst_delay = 7,
                        start_delay = 200;

    // clock and reset
    logic   [0 : 0]     clk;
    logic   [0 : 0]     resetn;
    // control and data
    logic   [7 : 0]     comp;
    logic   [0 : 0]     cpol;
    logic   [0 : 0]     cpha;
    logic   [1 : 0]     tr_en;
    logic   [0 : 0]     msb_lsb;
    logic   [7 : 0]     tx_data;
    logic   [7 : 0]     rx_data;
    logic   [0 : 0]     tx_req;
    logic   [0 : 0]     tx_req_ack;
    logic   [0 : 0]     sck;
    logic   [0 : 0]     cs;
    logic   [0 : 0]     sdo;
    logic   [0 : 0]     sdi;

    spi_master
    spi_master_dut
    (
        // clock and reset
        .clk        ( clk           ),
        .resetn     ( resetn        ),
        // control and data
        .comp       ( comp          ),
        .cpol       ( cpol          ),
        .cpha       ( cpha          ),
        .tr_en      ( tr_en         ),
        .msb_lsb    ( msb_lsb       ),
        .tx_data    ( tx_data       ),
        .rx_data    ( rx_data       ),
        .tx_req     ( tx_req        ),
        .tx_req_ack ( tx_req_ack    ),
        .sck        ( sck           ),
        .cs         ( cs            ),
        .sdo        ( sdo           ),
        .sdi        ( sdi           )
    );

    initial
    begin
        #(start_delay);
        clk = '1;
        forever
            #(T/2)  clk = !clk;
    end
    initial
    begin
        #(start_delay);
        resetn = '0;
        repeat(rst_delay) @(posedge clk);
        resetn = '1;
    end
    initial
    begin
        #(start_delay);
        tx_req = '0;
        cpha = '0;
        cpol = '0;
        tx_data = '0;
        comp = '0;
        tr_en = '0;
        msb_lsb = '0;
        @(posedge resetn);
        repeat(repeat_n)
        begin
            #100;
            uart_write();
        end
        $stop;
    end

    initial
    begin
        sdi = '0;
        forever
        begin
            @(posedge sck);
            sdi = $urandom_range(0,1);
        end
    end

    task uart_write();
        tx_req = '1;
        tx_data = $urandom_range(0,255);
        case($urandom_range(0,9))
            0       : tx_data = 'x;
            default : ;
        endcase
        cpha = $urandom_range(0,1);
        cpol = $urandom_range(0,1);
        msb_lsb = $urandom_range(0,1);
        case( $urandom_range(0,9) )
            0       : comp = 0;
            1       : comp = 1;
            2       : comp = 2;
            3       : comp = 4;
            4       : comp = 8;
            5       : comp = 16;
            6       : comp = 32;
            7       : comp = 64;
            8       : comp = 128;
            9       : comp = 255;
            default : comp = 0;
        endcase
        tr_en = '1;
        @(posedge tx_req_ack);
        tx_req = '0;
        @(posedge clk);
    endtask : uart_write
    
endmodule : spi_master_tb

/*
*  File            :   spi_if.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.28
*  Language        :   SystemVerilog
*  Description     :   This is spi interface
*  Copyright(c)    :   2019 Vlasov D.V.
*/

interface spi_if #(parameter slave_c = 1)(input logic clk, input logic rst);

    logic   [slave_c-1 : 0]     ss;
    logic   [0         : 0]     sck;
    logic   [0         : 0]     mosi;
    wire    [0         : 0]     miso;

    logic   [slave_c-1 : 0]     miso_drv;
    logic   [0         : 0]     miso_mon;

    assign miso = ! ( $countbits(miso_drv,'1,'0) == 1 ) ? 'x : $countbits(miso_drv,'1);
    assign miso_mon = miso;

endinterface : spi_if

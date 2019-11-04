/*
*  File            :   ahb_lite_if.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.01.01
*  Language        :   SystemVerilog
*  Description     :   This is ahb lite interface
*  Copyright(c)    :   2019 Vlasov D.V.
*/

interface ahb_lite_if(
    input   logic   [0 : 0]    HCLK,
    input   logic   [0 : 0]    HRESETn
);

    logic   [31 : 0]    HADDR;
    logic   [2  : 0]    HBURST;
    logic   [0  : 0]    HMASTLOCK;
    logic   [3  : 0]    HPROT;
    logic   [0  : 0]    HSEL;
    logic   [2  : 0]    HSIZE;
    logic   [1  : 0]    HTRANS;
    logic   [31 : 0]    HWDATA;
    logic   [0  : 0]    HWRITE;
    logic   [0  : 0]    HREADY;
    logic   [31 : 0]    HRDATA;
    logic   [0  : 0]    HREADYOUT;
    logic   [0  : 0]    HRESP;

endinterface : ahb_lite_if

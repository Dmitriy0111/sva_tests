/*
*  File            :   sdram_if.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.01.01
*  Language        :   SystemVerilog
*  Description     :   This is sdram interface
*  Copyright(c)    :   2019 Vlasov D.V.
*/

interface sdram_if
#(
    parameter                       addr_bits = 12,
                                    ba_bits = 2,
                                    dq_bits = 16,
                                    dm_bits = 1
)();

    logic   [0             : 0]     clk;
    logic   [0             : 0]     cke;
    logic   [0             : 0]     csn;
    logic   [0             : 0]     rasn;
    logic   [0             : 0]     casn;
    logic   [0             : 0]     wen;
    logic   [addr_bits - 1 : 0]     addr;
    logic   [ba_bits - 1   : 0]     ba;
    wire    [dq_bits - 1   : 0]     dq;
    logic   [dm_bits - 1   : 0]     dqm;

endinterface : sdram_if

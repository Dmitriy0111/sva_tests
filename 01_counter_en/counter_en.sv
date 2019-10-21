/*
*  File            :   counter_en.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.17
*  Language        :   SystemVerilog
*  Description     :   This is simple counter with enable
*  Copyright(c)    :   2019 Vlasov D.V.
*/

module counter_en
#(
    parameter                   inc_dec = '1
)(
    input   logic   [0 : 0]     clk,
    input   logic   [0 : 0]     rst_n,
    input   logic   [0 : 0]     en,
    output  logic   [7 : 0]     cnt
);

    always_ff @(posedge clk, negedge rst_n)
        if( !rst_n )
            cnt <= '0;
        else
            if( en )
                cnt <= cnt + ( ( inc_dec == '1 ) ? 1'b1 : - 1'b1 );

    property inc;
        @(posedge clk)
        disable iff(!rst_n)
        en |-> ##1 cnt == $past(cnt) + 1'b1;
    endproperty : inc

    property unk;
        @(posedge clk)
        disable iff(!rst_n)
        !$isunknown(cnt);
    endproperty : unk

    inc_a : assert property(inc) else $display("Inc : Fail at time %tns",$time());
    inc_c : cover  property(inc)      ;//$display("Inc : Pass");
    unk_a : assert property(unk) else $display("Unk : Fail at time %tns",$time());
    unk_c : cover  property(unk)      ;//$display("Unk : Pass");

endmodule : counter_en

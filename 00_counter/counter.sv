/*
*  File            :   counter.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.17
*  Language        :   SystemVerilog
*  Description     :   This is simple counter
*  Copyright(c)    :   2019 Vlasov D.V.
*/

module counter
#(
    parameter                   inc_dec = '1
)(
    input   logic   [0 : 0]     clk,
    input   logic   [0 : 0]     rst_n,
    output  logic   [7 : 0]     cnt
);

    always_ff @(posedge clk, negedge rst_n)
        if( !rst_n )
            cnt <= '0;
        else
            cnt <= cnt + ( ( inc_dec == '1 ) ? 1'b1 : - 1'b1 );

    property inc;
        @(posedge clk)
        disable iff(!rst_n)
        $past(rst_n) |-> cnt == $past(cnt) + 1'b1;
    endproperty : inc

    property unk;
        @(posedge clk)
        disable iff(!rst_n)
        !$isunknown(cnt);
    endproperty : unk

    inc_a : assert property(inc) else $display("Inc : Fail at time %tns",$time());
    inc_c : cover  property(inc)      ;//$dislpay("Inc : Pass at time %tns",$time());
    unk_a : assert property(unk) else $display("Unk : Fail at time %tns",$time());
    unk_c : cover  property(unk)      ;//$display("Unk : Pass at time %tns",$time());

endmodule : counter

`include "common_settings.svh"

module counter_inc_dec
(
    input   logic   [0 : 0]     clk,
    input   logic   [0 : 0]     rst_n,
    input   logic   [0 : 0]     inc,
    input   logic   [0 : 0]     dec,
    output  logic   [7 : 0]     cnt
);

    always_ff @(posedge clk, negedge rst_n)
        if( !rst_n )
            cnt <= '0;
        else
            cnt <= cnt + ( ( inc == '1 ) ? 1'b1 : '0 ) + ( ( dec == '1 ) ? - 1'b1 : '0 );

    `ifdef ASSERTS_SV

    property inc_p;
        @(posedge clk)
        disable iff(!rst_n)
            ( inc && !dec ) |-> ##1 ( cnt != ( ( $past(cnt) == 8'hFF ) ? $past(cnt) + 1 : 8'h00 ) );
    endproperty : inc_p

    property dec_p;
        @(posedge clk)
        disable iff(!rst_n)
            ( dec && !inc ) |-> ##1 ( cnt != ( ( $past(cnt) == 8'h00 ) ? $past(cnt) - 1 : 8'hFF ) );
    endproperty : dec_p

    property unk_p;
        @(posedge clk)
        disable iff(!rst_n)
        !$isunknown(cnt);
    endproperty : unk_p

    inc_a : assert property(inc_p) else $display("Inc : Fail at time %tns",$time());
    inc_c : cover  property(inc_p)      ;// $display("Inc : Pass at time %tns",$time());
    dec_a : assert property(dec_p) else $display("dec : Fail at time %tns",$time());
    dec_c : cover  property(dec_p)      ;// $display("dec : Pass at time %tns",$time());
    unk_a : assert property(unk_p) else $display("Unk : Fail at time %tns",$time());
    unk_c : cover  property(unk_p)      ;//$display("Unk : Pass at time %tns",$time());
    
    `endif

endmodule : counter_inc_dec

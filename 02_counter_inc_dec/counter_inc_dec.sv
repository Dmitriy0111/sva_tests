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

    `define inc_e ( rst_n && en )

    property inc_dec;
        @(posedge clk)
        disable iff(!rst_n || !(dec || inc))
        $past(rst_n && (dec || inc)) |-> cnt == ( { inc , dec } == 2'b11 ? $past(cnt) : { inc , dec } == 2'b10 ? $past(cnt) + 1'b1 : { inc , dec } == 2'b01 ? $past(cnt) - 1'b1 : $past(cnt) );
    endproperty : inc_dec

    property unk;
        @(posedge clk)
        disable iff(!rst_n)
        !$isunknown(cnt);
    endproperty : unk

    inc_dec_a : assert property(inc_dec) else $display("Inc : Fail at time %tns",$time());
    unk_a : assert property(unk) else $display("Unk : Fail at time %tns",$time());
    
    `endif

endmodule : counter_inc_dec

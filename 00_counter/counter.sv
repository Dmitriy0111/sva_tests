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

    logic   [7 : 0]     count;

    assign cnt = count;

    always_ff @(posedge clk, negedge rst_n)
        if( !rst_n )
            count <= '0;
        else
            count <= count + ( ( inc_dec == '1 ) ? 1'b1 : - 1'b1 );

    property inc_test_p;
        @(posedge clk)
        disable iff(!rst_n)
        ( $past(rst_n) ) |-> ( count == $past(count) + 1'b1 );
    endproperty : inc_test_p

    property unk_test_p(test_v);
        @(posedge clk)
        disable iff(!rst_n)
        !$isunknown(count);
    endproperty : unk_test_p

    property rst_test_p(test_v);
        @(posedge clk)
        ( !rst_n ) |=> ( test_v == '0 );
    endproperty : rst_test_p

    inc_a : assert property( inc_test_p             ) else $warning("inc_a : FAIL");
    inc_c : cover  property( inc_test_p             )      ;// $info("inc_c : PASS");
    unk_a : assert property( unk_test_p( count )    ) else $warning("unk_a : FAIL");
    unk_c : cover  property( unk_test_p( count )    )      ;// $info("unk_c : PASS");
    rst_a : assert property( rst_test_p( count )    ) else $warning("rst_a : FAIL");
    rst_c : cover  property( rst_test_p( count )    )      ;// $info("rst_a : PASS");

endmodule : counter

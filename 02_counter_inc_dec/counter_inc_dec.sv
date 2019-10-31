/*
*  File            :   counter_inc_dec.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.17
*  Language        :   SystemVerilog
*  Description     :   This is counter
*  Copyright(c)    :   2019 Vlasov D.V.
*/

module counter_inc_dec
(
    input   logic   [0 : 0]     clk,
    input   logic   [0 : 0]     rst_n,
    input   logic   [0 : 0]     inc,
    input   logic   [0 : 0]     dec,
    output  logic   [7 : 0]     cnt
);

    logic   [7 : 0]     count;
    
    assign cnt = count;

    always_ff @(posedge clk, negedge rst_n)
        if( !rst_n )
            count <= '0;
        else
            count <= count + ( ( inc == '1 ) ? 1'b1 : '0 ) + ( ( dec == '1 ) ? - 1'b1 : '0 );

    property inc_test_p;
        @(posedge clk)
        disable iff(!rst_n)
        ( inc && !dec ) |=> ( count != ( ( $past(count) == 8'hFF ) ? $past(count) + 1 : 8'h00 ) );
    endproperty : inc_test_p

    property dec_test_p;
        @(posedge clk)
        disable iff(!rst_n)
        ( dec && !inc ) |=> ( count != ( ( $past(count) == 8'h00 ) ? $past(count) - 1 : 8'hFF ) );
    endproperty : dec_test_p

    property unk_test_p(test_v);
        @(posedge clk)
        disable iff(!rst_n)
        !$isunknown(test_v);
    endproperty : unk_test_p

    property hold_test_p(test_v);
        @(posedge clk)
        disable iff(!rst_n)
        ( !dec && !inc ) |=> $stable(test_v);
    endproperty : hold_test_p

    inc_a   : assert property( inc_test_p           ) else $warning("inc_a : FAIL");
    inc_c   : cover  property( inc_test_p           )      ;// $info("inc_c : PASS");
    dec_a   : assert property( dec_test_p           ) else $warning("dec_a : FAIL");
    dec_c   : cover  property( dec_test_p           )      ;// $info("dec_c : PASS");
    unk_a   : assert property( unk_test_p( count )  ) else $warning("unk_a : FAIL");
    unk_c   : cover  property( unk_test_p( count )  )      ;// $info("unk_c : PASS");
    hold_a  : assert property( hold_test_p( count ) ) else $warning("hold_a : FAIL");
    hold_c  : cover  property( hold_test_p( count ) )      ;// $info("hold_c : PASS");
    
endmodule : counter_inc_dec

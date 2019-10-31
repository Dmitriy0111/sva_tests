/*
*  File            :   counter_au.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.17
*  Language        :   SystemVerilog
*  Description     :   This is counter assert unit
*  Copyright(c)    :   2019 Vlasov D.V.
*/

module counter_au
(
    input   logic   [0 : 0]     clk,
    input   logic   [0 : 0]     rst_n,
    input   logic   [0 : 0]     inc,
    input   logic   [0 : 0]     dec,
    input   logic   [7 : 0]     cnt
);

    property inc_test_p;
        @(posedge clk)
        disable iff(!rst_n)
            ( inc && !dec ) |=> ( cnt != ( ( $past(cnt) == 8'hFF ) ? $past(cnt) + 1 : 8'h00 ) );
    endproperty : inc_test_p

    property dec_test_p;
        @(posedge clk)
        disable iff(!rst_n)
            ( dec && !inc ) |=> ( cnt != ( ( $past(cnt) == 8'h00 ) ? $past(cnt) - 1 : 8'hFF ) );
    endproperty : dec_test_p

    property unk_test_p;
        @(posedge clk)
        disable iff(!rst_n)
        !$isunknown(cnt);
    endproperty : unk_test_p

    property hold_test_p(test_v);
        @(posedge clk)
        disable iff(!rst_n)
        ( !dec && !inc ) |=> $stable(test_v);
    endproperty : hold_test_p

    inc_a   : assert property( inc_test_p           ) else $warning("inc_a %m : FAIL");
    inc_c   : cover  property( inc_test_p           )      ;// $info("inc_c : PASS");
    dec_a   : assert property( dec_test_p           ) else $warning("dec_a %m : FAIL");
    dec_c   : cover  property( dec_test_p           )      ;// $info("dec_c : PASS");
    unk_a   : assert property( unk_test_p           ) else $warning("unk_a %m : FAIL");
    unk_c   : cover  property( unk_test_p           )      ;// $info("unk_c : PASS");
    hold_a  : assert property( hold_test_p( cnt )   ) else $warning("hold_a %m : FAIL");
    hold_c  : cover  property( hold_test_p( cnt )   )      ;// $info("hold_c : PASS");

endmodule : counter_au

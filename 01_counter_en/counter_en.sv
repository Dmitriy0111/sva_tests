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

    property inc_p;
        @(posedge clk)
        disable iff(!rst_n)
        en |=> ( cnt == $past(cnt) + 1'b1 );
    endproperty : inc_p

    property unk_p;
        @(posedge clk)
        disable iff(!rst_n)
        !$isunknown(cnt);
    endproperty : unk_p

    property rst_p;
        @(posedge clk)
        ( !rst_n ) |=> ( cnt == '0 );
    endproperty : rst_p

    property hold_p;
        @(posedge clk)
        disable iff(!rst_n)
        ( !en ) |=> ( cnt == $past(cnt) );
    endproperty : hold_p

    inc_a   : assert property( inc_p    ) else $warning("inc_a : FAIL");
    inc_c   : cover  property( inc_p    )      ;//$info("inc_c : PASS");
    unk_a   : assert property( unk_p    ) else $warning("unk_a : FAIL");
    unk_c   : cover  property( unk_p    )      ;//$info("unk_c : PASS");
    rst_a   : assert property( rst_p    ) else $warning("rst_a : FAIL");
    rst_c   : cover  property( rst_p    )      ;//$info("rst_c : PASS");
    hold_a  : assert property( hold_p   ) else $warning("hold_a : FAIL");
    hold_c  : cover  property( hold_p   )      ;//$info("hold_c : PASS");

endmodule : counter_en

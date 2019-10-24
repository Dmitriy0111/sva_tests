/*
*  File            :   simple_spi_pm.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.24
*  Language        :   SystemVerilog
*  Description     :   This is property module for spi simple module
*  Copyright(c)    :   2019 Vlasov D.V.
*/

module simple_spi_pm
#(
    parameter                           SS_WIDTH = 1
)(
    input   wire                        clk_i,
    input   wire                        rst_i,

    input   wire    [7          : 0]    spcr,
    input   wire    [7          : 0]    sper,
    input   wire    [SS_WIDTH-1 : 0]    ss_r,
    input   wire    [7          : 0]    spsr,
    input   wire    [7          : 0]    rfdout,
    input   wire    [7          : 0]    dat_o,
    input   wire    [2          : 0]    adr_i

);

    property rst_test(test_v,comp_v);
        @(posedge clk_i) rst_i |=> (test_v == comp_v);
    endproperty : rst_test

    property test_out(test_addr,test_reg);
        @(posedge clk_i)
        disable iff( rst_i )
        ( adr_i == test_addr ) |=> ( dat_o == $past(test_reg) );
    endproperty : test_out
        
    property test_out_();
        @(posedge clk_i)
        disable iff( rst_i )
        if      ( adr_i == 3'b000 ) ( '1 |=> ( dat_o == $past(spcr)   ) )
        else if ( adr_i == 3'b001 ) ( '1 |=> ( dat_o == $past(spsr)   ) )
        else if ( adr_i == 3'b010 ) ( '1 |=> ( dat_o == $past(rfdout) ) )
        else if ( adr_i == 3'b011 ) ( '1 |=> ( dat_o == $past(sper)   ) )
        else if ( adr_i == 3'b100 ) ( '1 |=> ( dat_o == $past(ss_r)   ) )
        else                        ( '1 |=> ( dat_o == '0            ) );
        //case( adr_i )
        //    3'b000  :   ( '1 |=> ( dat_o == $past(spcr)   ) );
        //    3'b001  :   ( '1 |=> ( dat_o == $past(spsr)   ) );
        //    3'b010  :   ( '1 |=> ( dat_o == $past(rfdout) ) );
        //    3'b011  :   ( '1 |=> ( dat_o == $past(sper)   ) );
        //    3'b100  :   ( '1 |=> ( dat_o == $past(ss_r)   ) );
        //    default :   ( '1 |=> ( dat_o == '0            ) );
        //endcase
    endproperty : test_out_

    rst_spcr_a  : assert property( rst_test( spcr , 8'h10 ) ) else $warning("rst_spcr_a : FAIL");
    rst_spcr_c  : cover  property( rst_test( spcr , 8'h10 ) )      ;// $info("rst_spcr_c : PASS");

    rst_sper_a  : assert property( rst_test( sper , 8'h00 ) ) else $warning("rst_sper_a : FAIL");
    rst_sper_c  : cover  property( rst_test( sper , 8'h00 ) )      ;// $info("rst_sper_c : PASS");

    rst_ss_r_a  : assert property( rst_test( ss_r , '0    ) ) else $warning("rst_ss_r_a : FAIL");
    rst_ss_r_c  : cover  property( rst_test( ss_r , '0    ) )      ;// $info("rst_ss_r_c : PASS");

    test_out_spcr_a     : assert property( test_out( 3'b000 , spcr   ) ) else $warning("test_out_spcr_a : FAIL");
    test_out_spcr_c     : cover  property( test_out( 3'b000 , spcr   ) )      ;// $info("test_out_spcr_c : PASS");

    test_out_spsr_a     : assert property( test_out( 3'b001 , spsr   ) ) else $warning("test_out_spsr_a : FAIL");
    test_out_spsr_c     : cover  property( test_out( 3'b001 , spsr   ) )      ;// $info("test_out_spsr_c : PASS");

    test_out_sper_a     : assert property( test_out( 3'b011 , sper   ) ) else $warning("test_out_sper_a : FAIL");
    test_out_sper_c     : cover  property( test_out( 3'b011 , sper   ) )      ;// $info("test_out_sper_c : PASS");

    test_out_ss_r_a     : assert property( test_out( 3'b100 , ss_r   ) ) else $warning("test_out_ss_r_a : FAIL");
    test_out_ss_r_c     : cover  property( test_out( 3'b100 , ss_r   ) )      ;// $info("test_out_ss_r_c : PASS");

    test_out_rfdout_a   : assert property( test_out( 3'b010 , rfdout ) ) else $warning("test_out_rfdout_a : FAIL");
    test_out_rfdout_c   : cover  property( test_out( 3'b010 , rfdout ) )      ;// $info("test_out_rfdout_c : PASS");

    test_out_a : assert property( test_out_ );
    test_out_c : cover  property( test_out_ );

endmodule : simple_spi_pm

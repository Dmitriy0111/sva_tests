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
    input   wire    [0          : 0]    clk_i,
    input   wire    [0          : 0]    rst_i,
    input   wire    [7          : 0]    spcr,
    input   wire    [7          : 0]    sper,
    input   wire    [SS_WIDTH-1 : 0]    ss_r,
    input   wire    [7          : 0]    spsr,
    input   wire    [7          : 0]    rfdout,
    input   wire    [7          : 0]    dat_o,
    input   wire    [2          : 0]    adr_i,
    input   wire    [0          : 0]    spif,
    input   wire    [0          : 0]    wcol,
    input   wire    [11         : 0]    clkcnt,
    input   wire    [1          : 0]    state,
    input   wire    [3          : 0]    espr,
    input   wire    [2          : 0]    bcnt,
    input   wire    [7          : 0]    treg,
    input   wire    [0          : 0]    wfre,
    input   wire    [0          : 0]    rfwe,
    input   wire    [0          : 0]    sck_o,
    input   wire    [0          : 0]    wfempty,
    input   wire    [0          : 0]    ena
);

    wire    [0 : 0]     spe;

    assign spe = spcr[6];

    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                       Properties                                      //
    ///////////////////////////////////////////////////////////////////////////////////////////
    property rst_test(test_v,rst_cond,comp_v);
        @(posedge clk_i) ( rst_cond ) |=> ( test_v == comp_v );
    endproperty : rst_test
        
    property test_dat_o_p();
        @(posedge clk_i)
        disable iff( rst_i )
        if      ( adr_i == 3'b000 ) ( '1 |=> ( dat_o == $past(spcr)   ) )
        else if ( adr_i == 3'b001 ) ( '1 |=> ( dat_o == $past(spsr)   ) )
        else if ( adr_i == 3'b010 ) ( '1 |=> ( dat_o == $past(rfdout) || $isunknown(rfdout) ) )
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
    endproperty : test_dat_o_p

    property test_clock_div_p;
        @(posedge clk_i)
        disable iff( rst_i )
        if      ( spe & ( |clkcnt & |state ) ) ( '1 |=> ( clkcnt == ( $past(clkcnt) - 1'b1 ) ) )
        else if ( espr == 4'b0000            ) ( '1 |=> ( clkcnt == 12'h0                    ) )
        else if ( espr == 4'b0001            ) ( '1 |=> ( clkcnt == 12'h1                    ) )
        else if ( espr == 4'b0010            ) ( '1 |=> ( clkcnt == 12'h3                    ) )
        else if ( espr == 4'b0011            ) ( '1 |=> ( clkcnt == 12'hf                    ) )
        else if ( espr == 4'b0100            ) ( '1 |=> ( clkcnt == 12'h1f                   ) )
        else if ( espr == 4'b0101            ) ( '1 |=> ( clkcnt == 12'h7                    ) )
        else if ( espr == 4'b0110            ) ( '1 |=> ( clkcnt == 12'h3f                   ) )
        else if ( espr == 4'b0111            ) ( '1 |=> ( clkcnt == 12'h7f                   ) )
        else if ( espr == 4'b1000            ) ( '1 |=> ( clkcnt == 12'hff                   ) )
        else if ( espr == 4'b1001            ) ( '1 |=> ( clkcnt == 12'h1ff                  ) )
        else if ( espr == 4'b1010            ) ( '1 |=> ( clkcnt == 12'h3ff                  ) )
        else if ( espr == 4'b1011            ) ( '1 |=> ( clkcnt == 12'h7ff                  ) )
        else                                   ( '0                                            )
    endproperty : test_clock_div_p

    property state_change(c_state,cond,n_state);
        @(posedge clk_i)
        disable iff( rst_i )
        ( ( state == c_state ) && ( cond ) ) |=> ( state == n_state );
    endproperty : state_change
    
    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                  Assertions and covers                                //
    ///////////////////////////////////////////////////////////////////////////////////////////
    // check reset conditions
    rst_spcr_a      : assert property( rst_test( spcr  , rst_i        , 8'h10 ) ) else $warning("rst_spcr_a : FAIL");
    rst_spcr_c      : cover  property( rst_test( spcr  , rst_i        , 8'h10 ) )      ;// $info("rst_spcr_c : PASS");

    rst_sper_a      : assert property( rst_test( sper  , rst_i        , 8'h00 ) ) else $warning("rst_sper_a : FAIL");
    rst_sper_c      : cover  property( rst_test( sper  , rst_i        , 8'h00 ) )      ;// $info("rst_sper_c : PASS");

    rst_ss_r_a      : assert property( rst_test( ss_r  , rst_i        , '0    ) ) else $warning("rst_ss_r_a : FAIL");
    rst_ss_r_c      : cover  property( rst_test( ss_r  , rst_i        , '0    ) )      ;// $info("rst_ss_r_c : PASS");

    rst_spif_a      : assert property( rst_test( spif  , ~spe | rst_i , '0    ) ) else $warning("rst_spif_a : FAIL");
    rst_spif_c      : cover  property( rst_test( spif  , ~spe | rst_i , '0    ) )      ;// $info("rst_spif_c : PASS");

    rst_wcol_a      : assert property( rst_test( wcol  , ~spe | rst_i , '0    ) ) else $warning("rst_wcol_a : FAIL");
    rst_wcol_c      : cover  property( rst_test( wcol  , ~spe | rst_i , '0    ) )      ;// $info("rst_wcol_c : PASS");

    rst_state_a     : assert property( rst_test( state , ~spe | rst_i , '0    ) ) else $warning("rst_state_a : FAIL");
    rst_state_c     : cover  property( rst_test( state , ~spe | rst_i , '0    ) )      ;// $info("rst_state_c : PASS");

    rst_bcnt_a      : assert property( rst_test( bcnt  , ~spe | rst_i , '0    ) ) else $warning("rst_bcnt_a : FAIL");
    rst_bcnt_c      : cover  property( rst_test( bcnt  , ~spe | rst_i , '0    ) )      ;// $info("rst_bcnt_c : PASS");

    rst_treg_a      : assert property( rst_test( treg  , ~spe | rst_i , '0    ) ) else $warning("rst_treg_a : FAIL");
    rst_treg_c      : cover  property( rst_test( treg  , ~spe | rst_i , '0    ) )      ;// $info("rst_treg_c : PASS");

    rst_wfre_a      : assert property( rst_test( wfre  , ~spe | rst_i , '0    ) ) else $warning("rst_wfre_a : FAIL");
    rst_wfre_c      : cover  property( rst_test( wfre  , ~spe | rst_i , '0    ) )      ;// $info("rst_wfre_c : PASS");

    rst_rfwe_a      : assert property( rst_test( rfwe  , ~spe | rst_i , '0    ) ) else $warning("rst_rfwe_a : FAIL");
    rst_rfwe_c      : cover  property( rst_test( rfwe  , ~spe | rst_i , '0    ) )      ;// $info("rst_rfwe_c : PASS");

    rst_sck_o_a     : assert property( rst_test( sck_o , ~spe | rst_i , '0    ) ) else $warning("rst_sck_o_a : FAIL");
    rst_sck_o_c     : cover  property( rst_test( sck_o , ~spe | rst_i , '0    ) )      ;// $info("rst_sck_o_c : PASS");
    // check data output
    test_dat_o_a    : assert property( test_dat_o_p ) else $warning("test_dat_o_a : FAIL");
    test_dat_o_c    : cover  property( test_dat_o_p )      ;// $info("test_dat_o_c : PASS");
    // check clock div
    test_clock_div_a    : assert property( test_clock_div_p ) else $warning("test_clock_div_a : FAIL");
    test_clock_div_c    : cover  property( test_clock_div_p )      ;// $info("test_clock_div_c : PASS");
    // check FSM
    idle2clk_ph2_a      : assert property( state_change( 2'b00 , ~wfempty           , 2'b01 ) ) else $warning("idle2clk_ph2_a : FAIL");
    idle2clk_ph2_c      : cover  property( state_change( 2'b00 , ~wfempty           , 2'b01 ) )      ;// $info("idle2clk_ph2_c : PASS");

    clk_ph2_2clk_ph1_a  : assert property( state_change( 2'b01 , ena                , 2'b11 ) ) else $warning("clk_ph2_2clk_ph1_a : FAIL");
    clk_ph2_2clk_ph1_c  : cover  property( state_change( 2'b01 , ena                , 2'b11 ) )      ;// $info("clk_ph2_2clk_ph1_c : PASS");

    clk_ph1_2idle_a     : assert property( state_change( 2'b11 , ena && ( ~|bcnt )  , 2'b00 ) ) else $warning("clk_ph1_2idle_a : FAIL");
    clk_ph1_2idle_c     : cover  property( state_change( 2'b11 , ena && ( ~|bcnt )  , 2'b00 ) )      ;// $info("clk_ph1_2idle_c : PASS");

    clk_ph1_2clk_ph2_a  : assert property( state_change( 2'b11 , ena && !( ~|bcnt ) , 2'b01 ) ) else $warning("clk_ph1_2clk_ph2_a : FAIL");
    clk_ph1_2clk_ph2_c  : cover  property( state_change( 2'b11 , ena && !( ~|bcnt ) , 2'b01 ) )      ;// $info("clk_ph1_2clk_ph2_c : PASS");

endmodule : simple_spi_pm

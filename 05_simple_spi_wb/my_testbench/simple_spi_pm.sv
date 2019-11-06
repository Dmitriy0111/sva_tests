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
    property rst_test_p(test_v,rst_cond,comp_v);
        @(posedge clk_i) ( rst_cond ) |=> ( test_v == comp_v );
    endproperty : rst_test_p

    property test_clock_div_p;
        @(posedge clk_i)
        disable iff( rst_i )
        ( ( state == 2'b00 ) && ( ~wfempty ) ) |->
        if      ( espr == 4'b0000   ) ( ##[8*2    -2 :    8*2 + 2] ( state == 2'b11 ) ##1 ( state == 2'b00 ) )    // div = 2   -- original M68HC11 coding
        else if ( espr == 4'b0001   ) ( ##[8*4    -2 :    8*4 + 2] ( state == 2'b11 ) ##1 ( state == 2'b00 ) )    // div = 4   -- original M68HC11 coding
        else if ( espr == 4'b0010   ) ( ##[8*16   -2 :   8*16 + 2] ( state == 2'b11 ) ##1 ( state == 2'b00 ) )    // div = 16  -- original M68HC11 coding
        else if ( espr == 4'b0011   ) ( ##[8*32   -2 :   8*32 + 2] ( state == 2'b11 ) ##1 ( state == 2'b00 ) )    // div = 32  -- original M68HC11 coding
        else if ( espr == 4'b0100   ) ( ##[8*8    -2 :    8*8 + 2] ( state == 2'b11 ) ##1 ( state == 2'b00 ) )    // div = 8
        else if ( espr == 4'b0101   ) ( ##[8*64   -2 :   8*64 + 2] ( state == 2'b11 ) ##1 ( state == 2'b00 ) )    // div = 64
        else if ( espr == 4'b0110   ) ( ##[8*128  -2 :  8*128 + 2] ( state == 2'b11 ) ##1 ( state == 2'b00 ) )    // div = 128
        else if ( espr == 4'b0111   ) ( ##[8*256  -2 :  8*256 + 2] ( state == 2'b11 ) ##1 ( state == 2'b00 ) )    // div = 256
        else if ( espr == 4'b1000   ) ( ##[8*512  -2 :  8*512 + 2] ( state == 2'b11 ) ##1 ( state == 2'b00 ) )    // div = 512
        else if ( espr == 4'b1001   ) ( ##[8*1024 -2 : 8*1024 + 2] ( state == 2'b11 ) ##1 ( state == 2'b00 ) )    // div = 1024
        else if ( espr == 4'b1010   ) ( ##[8*2048 -2 : 8*2048 + 2] ( state == 2'b11 ) ##1 ( state == 2'b00 ) )    // div = 2048
        else if ( espr == 4'b1011   ) ( ##[8*4096 -2 : 8*4096 + 2] ( state == 2'b11 ) ##1 ( state == 2'b00 ) )    // div = 4096
        else                          ( '0                                                                   )
    endproperty : test_clock_div_p

    property state_change_p(c_state,cond,n_state);
        @(posedge clk_i)
        disable iff( rst_i )
        ( ( state == c_state ) && ( cond ) ) |=> ( state == n_state );
    endproperty : state_change_p
    
    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                  Assertions and covers                                //
    ///////////////////////////////////////////////////////////////////////////////////////////
    // check reset conditions
    rst_spcr_a      : assert property( rst_test_p( spcr  , rst_i        , 8'h10 )   ) else $warning("rst_spcr_a : FAIL");
    rst_spcr_c      : cover  property( rst_test_p( spcr  , rst_i        , 8'h10 )   )      ;// $info("rst_spcr_c : PASS");

    rst_sper_a      : assert property( rst_test_p( sper  , rst_i        , 8'h00 )   ) else $warning("rst_sper_a : FAIL");
    rst_sper_c      : cover  property( rst_test_p( sper  , rst_i        , 8'h00 )   )      ;// $info("rst_sper_c : PASS");

    rst_ss_r_a      : assert property( rst_test_p( ss_r  , rst_i        , '0    )   ) else $warning("rst_ss_r_a : FAIL");
    rst_ss_r_c      : cover  property( rst_test_p( ss_r  , rst_i        , '0    )   )      ;// $info("rst_ss_r_c : PASS");

    rst_spif_a      : assert property( rst_test_p( spif  , ~spe | rst_i , '0    )   ) else $warning("rst_spif_a : FAIL");
    rst_spif_c      : cover  property( rst_test_p( spif  , ~spe | rst_i , '0    )   )      ;// $info("rst_spif_c : PASS");

    rst_wcol_a      : assert property( rst_test_p( wcol  , ~spe | rst_i , '0    )   ) else $warning("rst_wcol_a : FAIL");
    rst_wcol_c      : cover  property( rst_test_p( wcol  , ~spe | rst_i , '0    )   )      ;// $info("rst_wcol_c : PASS");

    rst_state_a     : assert property( rst_test_p( state , ~spe | rst_i , '0    )   ) else $warning("rst_state_a : FAIL");
    rst_state_c     : cover  property( rst_test_p( state , ~spe | rst_i , '0    )   )      ;// $info("rst_state_c : PASS");

    rst_bcnt_a      : assert property( rst_test_p( bcnt  , ~spe | rst_i , '0    )   ) else $warning("rst_bcnt_a : FAIL");
    rst_bcnt_c      : cover  property( rst_test_p( bcnt  , ~spe | rst_i , '0    )   )      ;// $info("rst_bcnt_c : PASS");

    rst_treg_a      : assert property( rst_test_p( treg  , ~spe | rst_i , '0    )   ) else $warning("rst_treg_a : FAIL");
    rst_treg_c      : cover  property( rst_test_p( treg  , ~spe | rst_i , '0    )   )      ;// $info("rst_treg_c : PASS");

    rst_wfre_a      : assert property( rst_test_p( wfre  , ~spe | rst_i , '0    )   ) else $warning("rst_wfre_a : FAIL");
    rst_wfre_c      : cover  property( rst_test_p( wfre  , ~spe | rst_i , '0    )   )      ;// $info("rst_wfre_c : PASS");

    rst_rfwe_a      : assert property( rst_test_p( rfwe  , ~spe | rst_i , '0    )   ) else $warning("rst_rfwe_a : FAIL");
    rst_rfwe_c      : cover  property( rst_test_p( rfwe  , ~spe | rst_i , '0    )   )      ;// $info("rst_rfwe_c : PASS");

    rst_sck_o_a     : assert property( rst_test_p( sck_o , ~spe | rst_i , '0    )   ) else $warning("rst_sck_o_a : FAIL");
    rst_sck_o_c     : cover  property( rst_test_p( sck_o , ~spe | rst_i , '0    )   )      ;// $info("rst_sck_o_c : PASS");
    // check clock div
    test_clock_div_a    : assert property( test_clock_div_p ) else $warning("test_clock_div_a : FAIL");
    test_clock_div_c    : cover  property( test_clock_div_p )      ;// $info("test_clock_div_c : PASS");
    // check FSM
    idle2clk_ph2_a      : assert property( state_change_p( 2'b00 , ~wfempty           , 2'b01 ) ) else $warning("idle2clk_ph2_a : FAIL");
    idle2clk_ph2_c      : cover  property( state_change_p( 2'b00 , ~wfempty           , 2'b01 ) )      ;// $info("idle2clk_ph2_c : PASS");

    clk_ph2_2clk_ph1_a  : assert property( state_change_p( 2'b01 , ena                , 2'b11 ) ) else $warning("clk_ph2_2clk_ph1_a : FAIL");
    clk_ph2_2clk_ph1_c  : cover  property( state_change_p( 2'b01 , ena                , 2'b11 ) )      ;// $info("clk_ph2_2clk_ph1_c : PASS");

    clk_ph1_2idle_a     : assert property( state_change_p( 2'b11 , ena && ( ~|bcnt )  , 2'b00 ) ) else $warning("clk_ph1_2idle_a : FAIL");
    clk_ph1_2idle_c     : cover  property( state_change_p( 2'b11 , ena && ( ~|bcnt )  , 2'b00 ) )      ;// $info("clk_ph1_2idle_c : PASS");

    clk_ph1_2clk_ph2_a  : assert property( state_change_p( 2'b11 , ena && !( ~|bcnt ) , 2'b01 ) ) else $warning("clk_ph1_2clk_ph2_a : FAIL");
    clk_ph1_2clk_ph2_c  : cover  property( state_change_p( 2'b11 , ena && !( ~|bcnt ) , 2'b01 ) )      ;// $info("clk_ph1_2clk_ph2_c : PASS");

endmodule : simple_spi_pm

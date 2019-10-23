/*
*  File            :   spi_master.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.22
*  Language        :   SystemVerilog
*  Description     :   This is spi master module
*  Copyright(c)    :   2019 Vlasov D.V.
*/

module spi_master
(
    // clock and reset
    input   logic   [0 : 0]     clk,        
    input   logic   [0 : 0]     resetn,     
    // control and data
    input   logic   [7 : 0]     comp,       
    input   logic   [0 : 0]     cpol,   
    input   logic   [0 : 0]     cpha,   
    input   logic   [1 : 0]     tr_en,  
    input   logic   [0 : 0]     msb_lsb,    
    input   logic   [7 : 0]     tx_data,    
    output  logic   [7 : 0]     rx_data,    
    input   logic   [0 : 0]     tx_req, 
    output  logic   [0 : 0]     tx_req_ack,
    output  logic   [0 : 0]     sck,
    output  logic   [0 : 0]     cs,
    output  logic   [0 : 0]     sdo,
    input   logic   [0 : 0]     sdi
);
    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                   Logic declaration                                   //
    ///////////////////////////////////////////////////////////////////////////////////////////
    logic   [7 : 0]     data_int;
    logic   [0 : 0]     cpol_int;
    logic   [0 : 0]     cpha_int;
    logic   [7 : 0]     comp_int;
    logic   [0 : 0]     msb_lsb_int;
    logic   [7 : 0]     comp_c;
    logic   [3 : 0]     bit_c;
    logic   [0 : 0]     sck_int;

    logic   [0 : 0]     idle2tr;
    logic   [0 : 0]     tr2post_tr;
    logic   [0 : 0]     post_tr2wait;
    logic   [0 : 0]     wait2idle;

    enum
    logic   [2 : 0]     { IDLE_s, TRANSMIT_s, POST_TR_s, WAIT_s } state, next_state;
    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                        Assigns                                        //
    ///////////////////////////////////////////////////////////////////////////////////////////
    assign idle2tr      = tx_req == '1;
    assign tr2post_tr   = (comp_c >= comp_int) && (bit_c == 15);
    assign post_tr2wait = (comp_c >= comp_int);
    assign wait2idle    = tx_req == '0;

    assign sck = sck_int ^ cpol_int;
    assign rx_data = data_int;
    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                         Always                                        //
    ///////////////////////////////////////////////////////////////////////////////////////////
    always_ff @(posedge clk, negedge resetn)
        if( !resetn )
            state <= IDLE_s;
        else
            state <= tr_en ? next_state : IDLE_s;

    always_comb
    begin
        next_state = state;
        case( state )
            IDLE_s      : next_state = idle2tr      ? TRANSMIT_s : state;
            TRANSMIT_s  : next_state = tr2post_tr   ? POST_TR_s  : state;
            POST_TR_s   : next_state = post_tr2wait ? WAIT_s     : state;
            WAIT_s      : next_state = wait2idle    ? IDLE_s     : state;
            default     : next_state = IDLE_s;
        endcase
    end

    always_ff @(posedge clk, negedge resetn)
    begin
        if( !resetn )
        begin
            data_int <= '0;
            cpol_int <= '0;
            cpha_int <= '0;
            comp_int <= '0;
            comp_c <= '0;
            bit_c <= '0;
            tx_req_ack <= '0;
            sck_int <= '0;
            cs <= '1;
            sdo <= '1;
            msb_lsb_int <= '0;
        end
        else
        begin
            if( tr_en )
                case( state )
                    IDLE_s      :
                        begin
                            if( idle2tr )
                            begin
                                cpol_int <= cpol;
                                cpha_int <= cpha;
                                data_int <= tx_data;
                                comp_int <= comp;
                                msb_lsb_int <= msb_lsb;
                            end
                        end
                    TRANSMIT_s  :
                        begin
                            cs <= '0;
                            comp_c <= comp_c + 1'b1;
                            if( ( ~ cpha_int ) && ( comp_c == '0 ) )
                            begin
                                if( ~bit_c[0] )
                                    sdo <= msb_lsb_int ? data_int[7] : data_int[0];
                                else
                                    data_int <= msb_lsb_int ? { data_int[6 : 0] , sdi } : { sdi , data_int[7 : 1] };
                            end
                            else if( cpha_int && ( comp_c >= comp_int ) )
                            begin
                                if( ~bit_c[0] )
                                    sdo <= msb_lsb_int ? data_int[7] : data_int[0];
                                else
                                    data_int <= msb_lsb_int ? { data_int[6 : 0] , sdi } : { sdi , data_int[7 : 1] };
                            end
                            if( comp_c >= comp_int )
                            begin
                                sck_int <= ~ sck_int;
                                bit_c <= bit_c + 1'b1;
                                comp_c <= '0;
                                if( tr2post_tr )
                                    bit_c <= '0;
                            end
                        end
                    POST_TR_s   :
                        begin
                            comp_c <= comp_c + 1'b1;
                            if( post_tr2wait )
                            begin
                                comp_c <= '0;
                            end
                        end
                    WAIT_s      :
                        begin
                            cs <= '1;
                            tx_req_ack <= '1;
                            if( wait2idle )
                                tx_req_ack <= '0;
                        end
                    default     : ;
                endcase
            else
            begin
                data_int <= '0;
                cpol_int <= '0;
                cpha_int <= '0;
                comp_int <= '0;
                comp_c <= '0;
                bit_c <= '0;
                tx_req_ack <= '0;
                sck_int <= '0;
                cs <= '1;
                sdo <= '1;
                msb_lsb_int <= '0;
            end
        end
    end

    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                       Properties                                      //
    ///////////////////////////////////////////////////////////////////////////////////////////
    // reset test property
    property rst_test(test_v,comp_v);
        @(posedge clk) ( !resetn ) |=> ( test_v == comp_v );
    endproperty : rst_test
    // unknown test property
    property unk_test(test_v);
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( tx_req && ( state == IDLE_s ) ) |=> ( ! $isunknown(test_v) );
    endproperty : unk_test
    // check state_changing
    property state_change(c_state,cond,n_state);
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( ( state == c_state ) && ( cond == '1 ) ) |=> ( state == n_state );
    endproperty : state_change
    // check state_changing
    property state_change_(c_state,logic [2 : 0] n_state[]);
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( state == c_state ) |=> ( $stable(state) || ( test_state(state,n_state) == '1 ) );
    endproperty : state_change_
    //
    function bit test_state(logic [2 : 0] c_state, logic [2 : 0] n_state[]);
        foreach( n_state[i] )
            if( n_state[i] == c_state )
                return '1;
        return '0;
    endfunction : test_state
    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                  Assertions and covers                                //
    ///////////////////////////////////////////////////////////////////////////////////////////

    rst_data_int_a      : assert property( rst_test( data_int    , '0 )     ) else $warning("rst_data_int_a: FAIL");
    rst_data_int_c      : cover  property( rst_test( data_int    , '0 )     )      ;// $info("rst_data_int_c: PASS");

    rst_cpol_int_a      : assert property( rst_test( cpol_int    , '0 )     ) else $warning("rst_cpol_int_a: FAIL");
    rst_cpol_int_c      : cover  property( rst_test( cpol_int    , '0 )     )      ;// $info("rst_cpol_int_c: PASS");

    rst_cpha_int_a      : assert property( rst_test( cpha_int    , '0 )     ) else $warning("rst_cpha_int_a: FAIL");
    rst_cpha_int_c      : cover  property( rst_test( cpha_int    , '0 )     )      ;// $info("rst_cpha_int_c: PASS");

    rst_comp_int_a      : assert property( rst_test( comp_int    , '0 )     ) else $warning("rst_comp_int_a: FAIL");
    rst_comp_int_c      : cover  property( rst_test( comp_int    , '0 )     )      ;// $info("rst_comp_int_c: PASS");

    rst_comp_c_a        : assert property( rst_test( comp_c      , '0 )     ) else $warning("rst_comp_c_a: FAIL");
    rst_comp_c_c        : cover  property( rst_test( comp_c      , '0 )     )      ;// $info("rst_comp_c_c: PASS");

    rst_bit_c_a         : assert property( rst_test( bit_c       , '0 )     ) else $warning("rst_bit_c_a: FAIL");
    rst_bit_c_c         : cover  property( rst_test( bit_c       , '0 )     )      ;// $info("rst_bit_c_c: PASS");

    rst_tx_req_ack_a    : assert property( rst_test( tx_req_ack  , '0 )     ) else $warning("rst_tx_req_ack_a: FAIL");
    rst_tx_req_ack_c    : cover  property( rst_test( tx_req_ack  , '0 )     )      ;// $info("rst_tx_req_ack_c: PASS");

    rst_sck_int_a       : assert property( rst_test( sck_int     , '0 )     ) else $warning("rst_sck_int_a: FAIL");
    rst_sck_int_c       : cover  property( rst_test( sck_int     , '0 )     )      ;// $info("rst_sck_int_c: PASS");

    rst_cs_a            : assert property( rst_test( cs          , '1 )     ) else $warning("rst_cs_a: FAIL");
    rst_cs_c            : cover  property( rst_test( cs          , '1 )     )      ;// $info("rst_cs_c: PASS");

    rst_sdo_a           : assert property( rst_test( sdo         , '1 )     ) else $warning("rst_sdo_a: FAIL");
    rst_sdo_c           : cover  property( rst_test( sdo         , '1 )     )      ;// $info("rst_sdo_c: PASS");

    rst_msb_lsb_int_a   : assert property( rst_test( msb_lsb_int , '0 )     ) else $warning("rst_msb_lsb_int_a: FAIL");
    rst_msb_lsb_int_c   : cover  property( rst_test( msb_lsb_int , '0 )     )      ;// $info("rst_msb_lsb_int_c: PASS");

    unk_data_int_a      : assert property( unk_test( data_int )     ) else $warning("unk_data_int_a: FAIL");
    unk_data_int_c      : cover  property( unk_test( data_int )     )      ;// $info("unk_data_int_c: PASS");

    unk_cpol_int_a      : assert property( unk_test( cpol_int )     ) else $warning("unk_cpol_int_a: FAIL");
    unk_cpol_int_c      : cover  property( unk_test( cpol_int )     )      ;// $info("unk_cpol_int_c: PASS");

    unk_cpha_int_a      : assert property( unk_test( cpha_int )     ) else $warning("unk_cpha_int_a: FAIL");
    unk_cpha_int_c      : cover  property( unk_test( cpha_int )     )      ;// $info("unk_cpha_int_c: PASS");

    unk_comp_int_a      : assert property( unk_test( comp_int )     ) else $warning("unk_comp_int_a: FAIL");
    unk_comp_int_c      : cover  property( unk_test( comp_int )     )      ;// $info("unk_comp_int_c: PASS");

    idle_change_a       : assert property( state_change_( IDLE_s     , { TRANSMIT_s } )     ) else $warning("idle_change_a: FAIL");
    idle_change_c       : cover  property( state_change_( IDLE_s     , { TRANSMIT_s } )     )      ;// $info("idle_change_c: PASS");

    transmit_change_a   : assert property( state_change_( TRANSMIT_s , { POST_TR_s  } )     ) else $warning("transmit_change_a: FAIL");
    transmit_change_c   : cover  property( state_change_( TRANSMIT_s , { POST_TR_s  } )     )      ;// $info("transmit_change_c: PASS");

    post_tr_change_a    : assert property( state_change_( POST_TR_s  , { WAIT_s     } )     ) else $warning("post_tr_change_a: FAIL");
    post_tr_change_c    : cover  property( state_change_( POST_TR_s  , { WAIT_s     } )     )      ;// $info("post_tr_change_c: PASS");
    
    wait_change_a       : assert property( state_change_( WAIT_s     , { IDLE_s     } )     ) else $warning("wait_change_a: FAIL");
    wait_change_c       : cover  property( state_change_( WAIT_s     , { IDLE_s     } )     )      ;// $info("wait_change_c: PASS");

    idle2tr_a           : assert property( state_change( IDLE_s     , idle2tr      , TRANSMIT_s )   ) else $warning("idle2tr_a: FAIL");
    idle2tr_c           : cover  property( state_change( IDLE_s     , idle2tr      , TRANSMIT_s )   )      ;// $info("idle2tr_c: PASS");

    tr2post_tr_a        : assert property( state_change( TRANSMIT_s , tr2post_tr   , POST_TR_s  )   ) else $warning("tr2post_tr_a: FAIL");
    tr2post_tr_c        : cover  property( state_change( TRANSMIT_s , tr2post_tr   , POST_TR_s  )   )      ;// $info("tr2post_tr_c: PASS");

    post_tr2wait_a      : assert property( state_change( POST_TR_s  , post_tr2wait , WAIT_s     )   ) else $warning("post_tr2wait_a: FAIL");
    post_tr2wait_c      : cover  property( state_change( POST_TR_s  , post_tr2wait , WAIT_s     )   )      ;// $info("post_tr2wait_c: PASS");

    wait2idle_a         : assert property( state_change( WAIT_s     , wait2idle    , IDLE_s     )   ) else $warning("wait2idle_a: FAIL");
    wait2idle_c         : cover  property( state_change( WAIT_s     , wait2idle    , IDLE_s     )   )      ;// $info("wait2idle_c: PASS");
    
endmodule : spi_master

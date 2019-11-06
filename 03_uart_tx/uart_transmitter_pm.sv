/*
*  File            :   uart_transmitter_pm.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.23
*  Language        :   SystemVerilog
*  Description     :   This is uart transmitter property module
*  Copyright(c)    :   2019 Vlasov D.V.
*/

module uart_transmitter_pm
(
    input   wire    [0  : 0]    clk,
    input   wire    [0  : 0]    resetn,
    input   wire    [0  : 0]    tr_en,
    input   wire    [0  : 0]    tx_req,
    input   wire    [0  : 0]    idle2start,
    input   wire    [0  : 0]    start2tr,
    input   wire    [0  : 0]    tr2stop,
    input   wire    [0  : 0]    stop2wait,
    input   wire    [0  : 0]    wait2idle,
    input   wire    [2  : 0]    state,
    input   wire    [7  : 0]    tx_data_int,
    input   wire    [15 : 0]    comp_int,
    input   wire    [1  : 0]    stop_sel_int,
    input   wire    [15 : 0]    comp_c,
    input   wire    [3  : 0]    bit_c,
    input   wire    [0  : 0]    tx_req_ack,
    input   wire    [0  : 0]    uart_tx
);

    enum
    logic   [2  : 0]    { IDLE_s, START_s, TRANSMIT_s, STOP_s, WAIT_s } fsm_states;

    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                       Properties                                      //
    ///////////////////////////////////////////////////////////////////////////////////////////
    // ack answer for req property
    property req_ack_p;
        @(posedge clk) disable iff( !resetn )
        ( tx_req && tr_en && ( state == IDLE_s ) ) |=> ##[20:$] tx_req_ack;
    endproperty : req_ack_p
    // test unknown property data
    property unk_test_p(test_v);
        @(posedge clk) disable iff( !resetn )
        ( tx_req && tr_en && ( state == IDLE_s ) ) |=> !$isunknown(test_v);
    endproperty : unk_test_p
    // reset test value
    property rst_test_p(test_v,comp_v);
        @(posedge clk) 
        ( !resetn ) |=> ( test_v == comp_v )
    endproperty : rst_test_p
    // check state_changing
    property state_change_p(current_state,cond,next_state);
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( ( state == current_state ) && ( cond == '1 ) ) |=> ( state == next_state );
    endproperty : state_change_p

    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                  Assertions and covers                                //
    ///////////////////////////////////////////////////////////////////////////////////////////
    // state changing
    idle2start_a        : assert property( state_change_p( IDLE_s     , idle2start , START_s    )   ) else $warning("idle2start: FAIL");
    idle2start_c        : cover  property( state_change_p( IDLE_s     , idle2start , START_s    )   )      ;// $info("idle2start: PASS");
    start2tr_a          : assert property( state_change_p( START_s    , start2tr   , TRANSMIT_s )   ) else $warning("start2tr: FAIL");
    start2tr_c          : cover  property( state_change_p( START_s    , start2tr   , TRANSMIT_s )   )      ;// $info("start2tr: PASS");
    tr2stop_a           : assert property( state_change_p( TRANSMIT_s , tr2stop    , STOP_s     )   ) else $warning("tr2stop: FAIL");
    tr2stop_c           : cover  property( state_change_p( TRANSMIT_s , tr2stop    , STOP_s     )   )      ;// $info("tr2stop: PASS");
    stop2wait_a         : assert property( state_change_p( STOP_s     , stop2wait  , WAIT_s     )   ) else $warning("stop2wait: FAIL");
    stop2wait_c         : cover  property( state_change_p( STOP_s     , stop2wait  , WAIT_s     )   )      ;// $info("stop2wait: PASS");
    wait2idle_a         : assert property( state_change_p( WAIT_s     , wait2idle  , IDLE_s     )   ) else $warning("wait2idle: FAIL");
    wait2idle_c         : cover  property( state_change_p( WAIT_s     , wait2idle  , IDLE_s     )   )      ;// $info("wait2idle: PASS");
    // internal tx_data, comp and stop_sel assertions and covers
    unk_tx_data_int_a   : assert property( unk_test_p( tx_data_int  )   ) else $warning("unk_tx_data_int_a: FAIL");
    unk_tx_data_int_c   : cover  property( unk_test_p( tx_data_int  )   )      ;// $info("unk_tx_data_int_c: PASS");
    unk_comp_int_a      : assert property( unk_test_p( comp_int     )   ) else $warning("unk_comp_int_a: FAIL");
    unk_comp_int_c      : cover  property( unk_test_p( comp_int     )   )      ;// $info("unk_comp_int_c: PASS");
    unk_stop_sel_int_a  : assert property( unk_test_p( stop_sel_int )   ) else $warning("unk_stop_sel_int_a: FAIL");
    unk_stop_sel_int_c  : cover  property( unk_test_p( stop_sel_int )   )      ;// $info("unk_stop_sel_int_c: PASS");
    // ack answer for req assertions and covers
    req_ack_a           : assert property( req_ack_p        ) else $warning("req_ack: FAIL");
    req_ack_c           : cover  property( req_ack_p        )      ;// $info("req_ack: PASS");
    // reset tx_data_int assertions and covers
    rst_tx_data_int_a   : assert property( rst_test_p( tx_data_int  , '0 )  ) else $warning("rst_tx_data_int: FAIL");
    rst_tx_data_int_c   : cover  property( rst_test_p( tx_data_int  , '0 )  )      ;// $info("rst_tx_data_int: PASS");    
    // reset stop_sel_int assertions and covers
    rst_stop_sel_int_a  : assert property( rst_test_p( stop_sel_int , '0 )  ) else $warning("rst_stop_sel_int: FAIL");
    rst_stop_sel_int_c  : cover  property( rst_test_p( stop_sel_int , '0 )  )      ;// $info("rst_stop_sel_int: PASS");
    // reset comp_c assertions and covers
    rst_comp_c_a        : assert property( rst_test_p( comp_c       , '0 )  ) else $warning("rst_comp_c: FAIL");
    rst_comp_c_c        : cover  property( rst_test_p( comp_c       , '0 )  )      ;// $info("rst_comp_c: PASS");
    // reset bit_c assertions and covers
    rst_bit_c_a         : assert property( rst_test_p( bit_c        , '0 )  ) else $warning("rst_bit_c: FAIL");
    rst_bit_c_c         : cover  property( rst_test_p( bit_c        , '0 )  )      ;// $info("rst_bit_c: PASS");
    // reset tx_req_ack assertions and covers
    rst_tx_req_ack_a    : assert property( rst_test_p( tx_req_ack   , '0 )  ) else $warning("rst_tx_req_ack: FAIL");
    rst_tx_req_ack_c    : cover  property( rst_test_p( tx_req_ack   , '0 )  )      ;// $info("rst_tx_req_ack: PASS");
    // reset uart_tx assertions and covers
    rst_uart_tx_a       : assert property( rst_test_p( uart_tx      , '1 )  ) else $warning("rst_uart_tx: FAIL");
    rst_uart_tx_c       : cover  property( rst_test_p( uart_tx      , '1 )  )      ;// $info("rst_uart_tx: PASS");
    // reset comp_int assertions and covers
    rst_comp_int_a      : assert property( rst_test_p( comp_int     , '0 )  ) else $warning("rst_comp_int: FAIL");
    rst_comp_int_c      : cover  property( rst_test_p( comp_int     , '0 )  )      ;// $info("rst_comp_int: PASS");
        
endmodule : uart_transmitter_pm
    
/*
*  File            :   uart_transmitter.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.21
*  Language        :   SystemVerilog
*  Description     :   This is uart transmitter module
*  Copyright(c)    :   2019 Vlasov D.V.
*/

module uart_transmitter
(
    // clock and reset
    input   logic   [0  : 0]    clk,            // clock signal
    input   logic   [0  : 0]    resetn,         // reset signal
    // control and data
    input   logic   [15 : 0]    comp,           // for setting baudrate
    input   logic   [1  : 0]    stop_sel,       // stop select
    input   logic   [0  : 0]    tr_en,          // transmitter enable
    input   logic   [7  : 0]    tx_data,        // data for transmit
    input   logic   [0  : 0]    tx_req,         // transmit request
    output  logic   [0  : 0]    tx_req_ack,     // transmit request acknowledge
    output  logic   [0  : 0]    uart_tx         // uart tx output
);
    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                   Logic declaration                                   //
    ///////////////////////////////////////////////////////////////////////////////////////////
    // internal signals
    logic   [7  : 0]    tx_data_int;
    logic   [1  : 0]    stop_sel_int;
    logic   [15 : 0]    comp_int;
    logic   [15 : 0]    comp_c;
    logic   [3  : 0]    bit_c;
    // state changing signals
    logic   [0  : 0]    idle2start;
    logic   [0  : 0]    start2tr;
    logic   [0  : 0]    tr2stop;
    logic   [0  : 0]    stop2wait;
    logic   [0  : 0]    wait2idle;
    // fsm states
    enum
    logic   [2  : 0]    { IDLE_s, START_s, TRANSMIT_s, STOP_s, WAIT_s } state, next_state;
    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                        Assigns                                        //
    ///////////////////////////////////////////////////////////////////////////////////////////
    assign idle2start   = tx_req == '1;
    assign start2tr     = comp_c >= comp_int;
    assign tr2stop      = (comp_c >= comp_int) && (bit_c == 7);
    assign stop2wait    = (comp_c >= ( comp_int >> 1 ) ) && (bit_c == stop_sel_int);
    assign wait2idle    = tx_req == '0;
    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                         Always                                        //
    ///////////////////////////////////////////////////////////////////////////////////////////
    always_ff @(posedge clk, negedge resetn)
        if( !resetn )
            state <= IDLE_s;
        else
            state <= tr_en ? next_state : IDLE_s;
    // state change logic
    always_comb
    begin
        next_state = state;
        case( state )
            IDLE_s      : next_state = idle2start ? START_s    : state;
            START_s     : next_state = start2tr   ? TRANSMIT_s : state;
            TRANSMIT_s  : next_state = tr2stop    ? STOP_s     : state;
            STOP_s      : next_state = stop2wait  ? WAIT_s     : state;
            WAIT_s      : next_state = wait2idle  ? IDLE_s     : state;
            default     : next_state = IDLE_s;
        endcase
    end
    // control and data logic
    always_ff @(posedge clk, negedge resetn)
    begin
        if( !resetn )
        begin
            tx_data_int <= '0;
            stop_sel_int <= '0;
            comp_c <= '0;
            bit_c <= '0;
            tx_req_ack <= '0;
            uart_tx <= '1;
            comp_int <= '0;
        end
        else
        begin
            if( tr_en )
                case( state )
                    IDLE_s      :
                        begin
                            if( idle2start )
                            begin
                                stop_sel_int <= stop_sel;
                                tx_data_int <= tx_data;
                                comp_int <= comp;
                            end
                        end
                    START_s     :
                        begin
                            uart_tx <= '0;
                            comp_c <= comp_c + 1'b1;
                            if( start2tr )
                            begin
                                comp_c <= '0;
                            end
                        end
                    TRANSMIT_s  :
                        begin
                            uart_tx <= tx_data_int[0];
                            comp_c <= comp_c + 1'b1;
                            if( comp_c >= comp_int )
                            begin
                                bit_c <= bit_c + 1'b1;
                                comp_c <= '0;
                                tx_data_int <= { 1'b0 , tx_data_int[7 : 1] };
                                if( tr2stop )
                                    bit_c <= '0;
                            end
                        end
                    STOP_s      :
                        begin
                            uart_tx <= '1;
                            comp_c <= comp_c + 1'b1;
                            if( comp_c >= ( comp_int >> 1 ) )
                            begin
                                bit_c <= bit_c + 1'b1;
                                comp_c <= '0;
                                if( stop2wait )
                                    bit_c <= '0;
                            end
                        end
                    WAIT_s      :
                        begin
                            tx_req_ack <= '1;
                            if( wait2idle )
                                tx_req_ack <= '0;
                        end
                    default     : ;
                endcase
            else
            begin
                tx_data_int <= '0;
                stop_sel_int <= '0;
                comp_c <= '0;
                bit_c <= '0;
                tx_req_ack <= '0;
                uart_tx <= '1;
                comp_int <= '0;
            end
        end
    end

    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                       Properties                                      //
    ///////////////////////////////////////////////////////////////////////////////////////////
    // ack answer for req property
    property req_ack_p;
        @(posedge clk) disable iff( !resetn )
        ( $rose(tx_req) && tr_en && ( state == IDLE_s ) ) |=> ##[20:$] tx_req_ack;
    endproperty : req_ack_p
    // test unknown property data
    property unk_value(test_v);
        @(posedge clk) disable iff( !resetn )
        ( tx_req && tr_en && ( state == IDLE_s ) ) |=> !$isunknown(test_v);
    endproperty : unk_value
    // reset test value
    property rst_value(test_v,comp_v);
        @(posedge clk) 
        !resetn |=> ( test_v == comp_v )
    endproperty : rst_value
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
    // state changing
    idle2start_a        : assert property( state_change( IDLE_s     , idle2start , START_s    ) ) else $warning("idle2start: FAIL");
    idle2start_c        : cover  property( state_change( IDLE_s     , idle2start , START_s    ) )      ;// $info("idle2start: PASS");
    start2tr_a          : assert property( state_change( START_s    , start2tr   , TRANSMIT_s ) ) else $warning("start2tr: FAIL");
    start2tr_c          : cover  property( state_change( START_s    , start2tr   , TRANSMIT_s ) )      ;// $info("start2tr: PASS");
    tr2stop_a           : assert property( state_change( TRANSMIT_s , tr2stop    , STOP_s     ) ) else $warning("tr2stop: FAIL");
    tr2stop_c           : cover  property( state_change( TRANSMIT_s , tr2stop    , STOP_s     ) )      ;// $info("tr2stop: PASS");
    stop2wait_a         : assert property( state_change( STOP_s     , stop2wait  , WAIT_s     ) ) else $warning("stop2wait: FAIL");
    stop2wait_c         : cover  property( state_change( STOP_s     , stop2wait  , WAIT_s     ) )      ;// $info("stop2wait: PASS");
    wait2idle_a         : assert property( state_change( WAIT_s     , wait2idle  , IDLE_s     ) ) else $warning("wait2idle: FAIL");
    wait2idle_c         : cover  property( state_change( WAIT_s     , wait2idle  , IDLE_s     ) )      ;// $info("wait2idle: PASS");

    idle_change_a       : assert property( state_change_( IDLE_s     , { START_s    } )     ) else $warning("idle_change: FAIL");
    idle_change_c       : cover  property( state_change_( IDLE_s     , { START_s    } )     )      ;// $info("idle_change: PASS");
    start_change_a      : assert property( state_change_( START_s    , { TRANSMIT_s } )     ) else $warning("start_change: FAIL");
    start_change_c      : cover  property( state_change_( START_s    , { TRANSMIT_s } )     )      ;// $info("start_change: PASS");
    tr_change_a         : assert property( state_change_( TRANSMIT_s , { STOP_s     } )     ) else $warning("tr_change: FAIL");
    tr_change_c         : cover  property( state_change_( TRANSMIT_s , { STOP_s     } )     )      ;// $info("tr_change: PASS");
    stop_change_a       : assert property( state_change_( STOP_s     , { WAIT_s     } )     ) else $warning("stop_change: FAIL");
    stop_change_c       : cover  property( state_change_( STOP_s     , { WAIT_s     } )     )      ;// $info("stop_change: PASS");
    wait_change_a       : assert property( state_change_( WAIT_s     , { IDLE_s     } )     ) else $warning("wait_change: FAIL");
    wait_change_c       : cover  property( state_change_( WAIT_s     , { IDLE_s     } )     )      ;// $info("wait_change: PASS");
    // internal tx_data, comp and stop_sel assertions and covers
    unk_tx_data_int_a   : assert property( unk_value( tx_data_int  )    ) else $warning("unk_tx_data_int_a: FAIL");
    unk_tx_data_int_c   : cover  property( unk_value( tx_data_int  )    )      ;// $info("unk_tx_data_int_c: PASS");
    unk_comp_int_a      : assert property( unk_value( comp_int     )    ) else $warning("unk_comp_int_a: FAIL");
    unk_comp_int_c      : cover  property( unk_value( comp_int     )    )      ;// $info("unk_comp_int_c: PASS");
    unk_stop_sel_int_a  : assert property( unk_value( stop_sel_int )    ) else $warning("unk_stop_sel_int_a: FAIL");
    unk_stop_sel_int_c  : cover  property( unk_value( stop_sel_int )    )      ;// $info("unk_stop_sel_int_c: PASS");
    // ack answer for req assertions and covers
    req_ack_a           : assert property( req_ack_p            ) else $warning("req_ack: FAIL");
    req_ack_c           : cover  property( req_ack_p            )      ;// $info("req_ack: PASS");
    // reset tx_data_int assertions and covers
    rst_tx_data_int_a   : assert property( rst_value( tx_data_int  , '0 )   ) else $warning("rst_tx_data_int: FAIL");
    rst_tx_data_int_c   : cover  property( rst_value( tx_data_int  , '0 )   )      ;// $info("rst_tx_data_int: PASS");    
    // reset stop_sel_int assertions and covers
    rst_stop_sel_int_a  : assert property( rst_value( stop_sel_int , '0 )   ) else $warning("rst_stop_sel_int: FAIL");
    rst_stop_sel_int_c  : cover  property( rst_value( stop_sel_int , '0 )   )      ;// $info("rst_stop_sel_int: PASS");
    // reset comp_c assertions and covers
    rst_comp_c_a        : assert property( rst_value( comp_c       , '0 )   ) else $warning("rst_comp_c: FAIL");
    rst_comp_c_c        : cover  property( rst_value( comp_c       , '0 )   )      ;// $info("rst_comp_c: PASS");
    // reset bit_c assertions and covers
    rst_bit_c_a         : assert property( rst_value( bit_c        , '0 )   ) else $warning("rst_bit_c: FAIL");
    rst_bit_c_c         : cover  property( rst_value( bit_c        , '0 )   )      ;// $info("rst_bit_c: PASS");
    // reset tx_req_ack assertions and covers
    rst_tx_req_ack_a    : assert property( rst_value( tx_req_ack   , '0 )   ) else $warning("rst_tx_req_ack: FAIL");
    rst_tx_req_ack_c    : cover  property( rst_value( tx_req_ack   , '0 )   )      ;// $info("rst_tx_req_ack: PASS");
    // reset uart_tx assertions and covers
    rst_uart_tx_a       : assert property( rst_value( uart_tx      , '1 )   ) else $warning("rst_uart_tx: FAIL");
    rst_uart_tx_c       : cover  property( rst_value( uart_tx      , '1 )   )      ;// $info("rst_uart_tx: PASS");
    // reset comp_int assertions and covers
    rst_comp_int_a      : assert property( rst_value( comp_int     , '0 )   ) else $warning("rst_comp_int: FAIL");
    rst_comp_int_c      : cover  property( rst_value( comp_int     , '0 )   )      ;// $info("rst_comp_int: PASS");
    
endmodule : uart_transmitter

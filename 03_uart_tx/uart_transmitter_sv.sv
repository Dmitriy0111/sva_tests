/*
*  File            :   uart_transmitter_sv.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.21
*  Language        :   SystemVerilog
*  Description     :   This is uart transmitter module
*  Copyright(c)    :   2019 Vlasov D.V.
*/

module uart_transmitter_sv
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
    // idle to start property
    property idle2start_p;
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( ( state == IDLE_s ) && ( idle2start == '1 ) ) |=> ( state == START_s );
    endproperty : idle2start_p
    // idle change property
    property idle_change_p;
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( state == IDLE_s ) |=> ( ( state == START_s ) || ( state == $past(state) ) );
    endproperty : idle_change_p
    // start to transmit property
    property start2tr_p;
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( ( state == START_s ) && ( start2tr == '1 ) ) |=> ( state == TRANSMIT_s );
    endproperty : start2tr_p
    // start change property
    property start_change_p;
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( state == START_s ) |=> ( ( state == TRANSMIT_s ) || ( state == $past(state) ) );
    endproperty : start_change_p
    // transmit to stop property
    property tr2stop_p;
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( ( state == TRANSMIT_s ) && ( tr2stop == '1 ) ) |=> ( state == STOP_s );
    endproperty : tr2stop_p
    // transmit change property
    property tr_change_p;
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( state == TRANSMIT_s ) |=> ( ( state == STOP_s ) || ( state == $past(state) ) );
    endproperty : tr_change_p
    // stop to wait property
    property stop2wait_p;
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( ( state == STOP_s ) && ( stop2wait == '1 ) ) |=> ( state == WAIT_s );
    endproperty : stop2wait_p
    // stop change property
    property stop_change_p;
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( state == STOP_s ) |=> ( ( state == WAIT_s ) || ( state == $past(state) ) );
    endproperty : stop_change_p
    // wait to idle property
    property wait2idle_p;
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( ( state == STOP_s ) && ( wait2idle == '1 ) ) |=> ( state == IDLE_s );
    endproperty : wait2idle_p
    // wait change property
    property wait_change_p;
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( state == WAIT_s ) |=> ( ( state == IDLE_s ) || ( state == $past(state) ) );
    endproperty : wait_change_p
    // tx data internal unknown property
    property tx_data_unk_p;
        @(posedge clk) disable iff( !resetn )
        ( tx_req && tr_en && ( state == IDLE_s ) ) |=> !$isunknown(tx_data_int);
    endproperty : tx_data_unk_p
    // comp internal unknown property
    property comp_unk_p;
        @(posedge clk) disable iff( !resetn )
        ( tx_req && tr_en && ( state == IDLE_s ) ) |=> !$isunknown(comp_int);
    endproperty : comp_unk_p
    // stop select internal unknown property
    property stop_sel_unk_p;
        @(posedge clk) disable iff( !resetn )
        ( tx_req && tr_en && ( state == IDLE_s ) ) |=> !$isunknown(stop_sel_int);
    endproperty : stop_sel_unk_p
    // ack answer for req property
    property req_ack_p;
        @(posedge clk) disable iff( !resetn )
        ( tx_req && tr_en && ( state == IDLE_s ) ) |=> ##[20:$] tx_req_ack;
    endproperty : req_ack_p
    // reset tx data internal property
    property rst_tx_data_int_p;
        @(posedge clk) 
        !resetn |=> ( tx_data_int == '0 )
    endproperty : rst_tx_data_int_p
    // reset stop select internal property
    property rst_stop_sel_int_p;
        @(posedge clk) 
        !resetn |=> ( stop_sel_int == '0 )
    endproperty : rst_stop_sel_int_p
    // reset comp counter property
    property rst_comp_c_p;
        @(posedge clk) 
        !resetn |=> ( comp_c == '0 )
    endproperty : rst_comp_c_p
    // reset bit counter property
    property rst_bit_c_p;
        @(posedge clk) 
        !resetn |=> ( bit_c == '0 )
    endproperty : rst_bit_c_p
    // reset tx req ack property
    property rst_tx_req_ack_p;
        @(posedge clk) 
        !resetn |=> ( tx_req_ack == '0 )
    endproperty : rst_tx_req_ack_p
    // reset uart tx reg property
    property rst_uart_tx_p;
        @(posedge clk) 
        !resetn |=> ( uart_tx == '1 )
    endproperty : rst_uart_tx_p
    // reset comp internal property
    property rst_comp_int_p;
        @(posedge clk) 
        !resetn |=> ( comp_int == '0 )
    endproperty : rst_comp_int_p

    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                  Assertions and covers                                //
    ///////////////////////////////////////////////////////////////////////////////////////////
    // idle state assertions and covers
    idle2start_a        : assert property( idle2start_p         ) else $display("idle2start: Fail at time %tns",$time());
    idle2start_c        : cover  property( idle2start_p         )      ;// $display("idle2start: Pass at time %tns",$time());
    idle_change_a       : assert property( idle_change_p        ) else $display("idle_change: Fail at time %tns",$time());
    idle_change_c       : cover  property( idle_change_p        )      ;// $display("idle_change: Pass at time %tns",$time());
    // start state assertions and covers
    start2tr_a          : assert property( start2tr_p           ) else $display("start2tr: Fail at time %tns",$time());
    start2tr_c          : cover  property( start2tr_p           )      ;// $display("start2tr: Pass at time %tns",$time());
    start_change_a      : assert property( start_change_p       ) else $display("start_change: Fail at time %tns",$time());
    start_change_c      : cover  property( start_change_p       )      ;// $display("start_change: Pass at time %tns",$time());
    // transmit state assertions and covers
    tr2stop_a           : assert property( tr2stop_p            ) else $display("tr2stop: Fail at time %tns",$time());
    tr2stop_c           : cover  property( tr2stop_p            )      ;// $display("tr2stop: Pass at time %tns",$time());
    tr_change_a         : assert property( tr_change_p          ) else $display("tr_change: Fail at time %tns",$time());
    tr_change_c         : cover  property( tr_change_p          )      ;// $display("tr_change: Pass at time %tns",$time());
    // stop state assertions and covers
    stop2wait_a         : assert property( stop2wait_p          ) else $display("stop2wait: Fail at time %tns",$time());
    stop2wait_c         : cover  property( stop2wait_p          )      ;// $display("stop2wait: Pass at time %tns",$time());
    stop_change_a       : assert property( stop_change_p        ) else $display("stop_change: Fail at time %tns",$time());
    stop_change_c       : cover  property( stop_change_p        )      ;// $display("stop_change: Pass at time %tns",$time());
    // wait state assertions and covers
    wait2idle_a         : assert property( wait2idle_p          ) else $display("wait2idle: Fail at time %tns",$time());
    wait2idle_c         : cover  property( wait2idle_p          )      ;// $display("wait2idle: Pass at time %tns",$time());
    wait_change_a       : assert property( wait_change_p        ) else $display("wait_change: Fail at time %tns",$time());
    wait_change_c       : cover  property( wait_change_p        )      ;// $display("wait_change: Pass at time %tns",$time());
    // internal tx_data, comp and stop_sel assertions and covers
    tx_data_unk_a       : assert property( tx_data_unk_p        ) else $display("tx_data_int_unk: Fail at time %tns",$time());
    tx_data_unk_c       : cover  property( tx_data_unk_p        )      ;// $display("tx_data_int_unk: Pass at time %tns",$time());
    comp_unk_a          : assert property( comp_unk_p           ) else $display("comp_int_unk: Fail at time %tns",$time());
    comp_unk_c          : cover  property( comp_unk_p           )      ;// $display("comp_int_unk: Pass at time %tns",$time());
    stop_sel_unk_a      : assert property( stop_sel_unk_p       ) else $display("stop_sel_int_unk: Fail at time %tns",$time());
    stop_sel_unk_c      : cover  property( stop_sel_unk_p       )      ;// $display("stop_sel_int_unk: Pass at time %tns",$time());
    // ack answer for req assertions and covers
    req_ack_a           : assert property( req_ack_p            ) else $display("req_ack: Fail at time %tns",$time());
    req_ack_c           : cover  property( req_ack_p            )      ;// $display("req_ack: Pass at time %tns",$time());
    // reset tx_data_int assertions and covers
    rst_tx_data_int_a   : assert property( rst_tx_data_int_p    ) else $display("rst_tx_data_int: Fail at time %tns",$time());
    rst_tx_data_int_c   : cover  property( rst_tx_data_int_p    )      ;// $display("rst_tx_data_int: Pass at time %tns",$time());    
    // reset stop_sel_int assertions and covers
    rst_stop_sel_int_a  : assert property( rst_stop_sel_int_p   ) else $display("rst_stop_sel_int: Fail at time %tns",$time());
    rst_stop_sel_int_c  : cover  property( rst_stop_sel_int_p   )      ;// $display("rst_stop_sel_int: Pass at time %tns",$time());
    // reset comp_c assertions and covers
    rst_comp_c_a        : assert property( rst_comp_c_p         ) else $display("rst_comp_c: Fail at time %tns",$time());
    rst_comp_c_c        : cover  property( rst_comp_c_p         )      ;// $display("rst_comp_c: Pass at time %tns",$time());
    // reset bit_c assertions and covers
    rst_bit_c_a         : assert property( rst_bit_c_p          ) else $display("rst_bit_c: Fail at time %tns",$time());
    rst_bit_c_c         : cover  property( rst_bit_c_p          )      ;// $display("rst_bit_c: Pass at time %tns",$time());
    // reset tx_req_ack assertions and covers
    rst_tx_req_ack_a    : assert property( rst_tx_req_ack_p     ) else $display("rst_tx_req_ack: Fail at time %tns",$time());
    rst_tx_req_ack_c    : cover  property( rst_tx_req_ack_p     )      ;// $display("rst_tx_req_ack: Pass at time %tns",$time());
    // reset uart_tx assertions and covers
    rst_uart_tx_a       : assert property( rst_uart_tx_p        ) else $display("rst_uart_tx: Fail at time %tns",$time());
    rst_uart_tx_c       : cover  property( rst_uart_tx_p        )      ;// $display("rst_uart_tx: Pass at time %tns",$time());
    // reset comp_int assertions and covers
    rst_comp_int_a      : assert property( rst_comp_int_p       ) else $display("rst_comp_int: Fail at time %tns",$time());
    rst_comp_int_c      : cover  property( rst_comp_int_p       )      ;// $display("rst_comp_int: Pass at time %tns",$time());
    
endmodule : uart_transmitter_sv

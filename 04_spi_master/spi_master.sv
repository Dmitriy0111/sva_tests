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
    property rst_data_int_p;
        @(posedge clk)  ( !resetn ) |=> ( data_int == '0 );
    endproperty : rst_data_int_p

    property rst_cpol_int_p;
        @(posedge clk)  ( !resetn ) |=> ( cpol_int == '0 );
    endproperty : rst_cpol_int_p

    property rst_cpha_int_p;
        @(posedge clk)  ( !resetn ) |=> ( cpha_int == '0 );
    endproperty : rst_cpha_int_p

    property rst_comp_int_p;
        @(posedge clk)  ( !resetn ) |=> ( comp_int == '0 );
    endproperty : rst_comp_int_p

    property rst_comp_c_p;
        @(posedge clk)  ( !resetn ) |=> ( comp_c == '0 );
    endproperty : rst_comp_c_p

    property rst_bit_c_p;
        @(posedge clk)  ( !resetn ) |=> ( bit_c == '0 );
    endproperty : rst_bit_c_p

    property rst_tx_req_ack_p;
        @(posedge clk)  ( !resetn ) |=> ( tx_req_ack == '0 );
    endproperty : rst_tx_req_ack_p

    property rst_sck_int_p;
        @(posedge clk)  ( !resetn ) |=> ( sck_int == '0 );
    endproperty : rst_sck_int_p

    property rst_cs_p;
        @(posedge clk)  ( !resetn ) |=> ( cs == '1 );
    endproperty : rst_cs_p

    property rst_sdo_p;
        @(posedge clk)  ( !resetn ) |=> ( sdo == '1 );
    endproperty : rst_sdo_p

    property rst_msb_lsb_int_p;
        @(posedge clk)  ( !resetn ) |=> ( msb_lsb_int == '0 );
    endproperty : rst_msb_lsb_int_p

    property unk_data_int_p;
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( tx_req && ( state == IDLE_s ) ) |=> ( ! $isunknown(data_int) );
    endproperty : unk_data_int_p
    property unk_cpol_int_p;
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( tx_req && ( state == IDLE_s ) ) |=> ( ! $isunknown(cpol_int) );
    endproperty : unk_cpol_int_p
    property unk_cpha_int_p;
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( tx_req && ( state == IDLE_s ) ) |=> ( ! $isunknown(cpha_int) );
    endproperty : unk_cpha_int_p
    property unk_comp_int_p;
        @(posedge clk) disable iff( !resetn || !tr_en )
        ( tx_req && ( state == IDLE_s ) ) |=> ( ! $isunknown(comp_int) );
    endproperty : unk_comp_int_p

    property idle_change_p;
        @(posedge clk) disable iff(!resetn || !tr_en)
        ( state == IDLE_s ) |=> ( ( state == $past(state) ) || ( state == TRANSMIT_s ) );
    endproperty : idle_change_p

    property transmit_change_p;
        @(posedge clk) disable iff(!resetn || !tr_en)
        ( state == TRANSMIT_s ) |=> ( ( state == $past(state) ) || ( state == POST_TR_s ) );
    endproperty : transmit_change_p

    property post_tr_change_p;
        @(posedge clk) disable iff(!resetn || !tr_en)
        ( state == POST_TR_s ) |=> ( ( state == $past(state) ) || ( state == WAIT_s ) );
    endproperty : post_tr_change_p

    property wait_change_p;
        @(posedge clk) disable iff(!resetn || !tr_en)
        ( state == WAIT_s ) |=> ( ( state == $past(state) ) || ( state == IDLE_s ) );
    endproperty : wait_change_p
    ///////////////////////////////////////////////////////////////////////////////////////////
    //                                  Assertions and covers                                //
    ///////////////////////////////////////////////////////////////////////////////////////////
    rst_data_int_a      : assert property( rst_data_int_p       ) else $display("rst_data_int_a: Fail at time %tns",$time());
    rst_data_int_c      : cover  property( rst_data_int_p       )      ;// $display("rst_data_int_c: Pass at time %tns",$time());

    rst_cpol_int_a      : assert property( rst_cpol_int_p       ) else $display("rst_cpol_int_a: Fail at time %tns",$time());
    rst_cpol_int_c      : cover  property( rst_cpol_int_p       )      ;// $display("rst_cpol_int_c: Pass at time %tns",$time());

    rst_cpha_int_a      : assert property( rst_cpha_int_p       ) else $display("rst_cpha_int_a: Fail at time %tns",$time());
    rst_cpha_int_c      : cover  property( rst_cpha_int_p       )      ;// $display("rst_cpha_int_c: Pass at time %tns",$time());

    rst_comp_int_a      : assert property( rst_comp_int_p       ) else $display("rst_comp_int_a: Fail at time %tns",$time());
    rst_comp_int_c      : cover  property( rst_comp_int_p       )      ;// $display("rst_comp_int_c: Pass at time %tns",$time());

    rst_comp_c_a        : assert property( rst_comp_c_p         ) else $display("rst_comp_c_a: Fail at time %tns",$time());
    rst_comp_c_c        : cover  property( rst_comp_c_p         )      ;// $display("rst_comp_c_c: Pass at time %tns",$time());

    rst_bit_c_a         : assert property( rst_bit_c_p          ) else $display("rst_bit_c_a: Fail at time %tns",$time());
    rst_bit_c_c         : cover  property( rst_bit_c_p          )      ;// $display("rst_bit_c_c: Pass at time %tns",$time());

    rst_tx_req_ack_a    : assert property( rst_tx_req_ack_p     ) else $display("rst_tx_req_ack_a: Fail at time %tns",$time());
    rst_tx_req_ack_c    : cover  property( rst_tx_req_ack_p     )      ;// $display("rst_tx_req_ack_c: Pass at time %tns",$time());

    rst_sck_int_a       : assert property( rst_sck_int_p        ) else $display("rst_sck_int_a: Fail at time %tns",$time());
    rst_sck_int_c       : cover  property( rst_sck_int_p        )      ;// $display("rst_sck_int_c: Pass at time %tns",$time());

    rst_cs_a            : assert property( rst_cs_p             ) else $display("rst_cs_a: Fail at time %tns",$time());
    rst_cs_c            : cover  property( rst_cs_p             )      ;// $display("rst_cs_c: Pass at time %tns",$time());

    rst_sdo_a           : assert property( rst_sdo_p            ) else $display("rst_sdo_a: Fail at time %tns",$time());
    rst_sdo_c           : cover  property( rst_sdo_p            )      ;// $display("rst_sdo_c: Pass at time %tns",$time());

    rst_msb_lsb_int_a   : assert property( rst_msb_lsb_int_p    ) else $display("rst_msb_lsb_int_a: Fail at time %tns",$time());
    rst_msb_lsb_int_c   : cover  property( rst_msb_lsb_int_p    )      ;// $display("rst_msb_lsb_int_c: Pass at time %tns",$time());

    unk_data_int_a      : assert property( unk_data_int_p       ) else $display("unk_data_int_a: Fail at time %tns",$time());
    unk_data_int_c      : cover  property( unk_data_int_p       )      ;// $display("unk_data_int_c: Pass at time %tns",$time());

    unk_cpol_int_a      : assert property( unk_cpol_int_p       ) else $display("unk_cpol_int_a: Fail at time %tns",$time());
    unk_cpol_int_c      : cover  property( unk_cpol_int_p       )      ;// $display("unk_cpol_int_c: Pass at time %tns",$time());

    unk_cpha_int_a      : assert property( unk_cpha_int_p       ) else $display("unk_cpha_int_a: Fail at time %tns",$time());
    unk_cpha_int_c      : cover  property( unk_cpha_int_p       )      ;// $display("unk_cpha_int_c: Pass at time %tns",$time());

    unk_comp_int_a      : assert property( unk_comp_int_p       ) else $display("unk_comp_int_a: Fail at time %tns",$time());
    unk_comp_int_c      : cover  property( unk_comp_int_p       )      ;// $display("unk_comp_int_c: Pass at time %tns",$time());

    idle_change_a       : assert property( idle_change_p        ) else $display("idle_change_a: Fail at time %tns",$time());
    idle_change_c       : cover  property( idle_change_p        )      ;// $display("idle_change_c: Pass at time %tns",$time());

    transmit_change_a   : assert property( transmit_change_p    ) else $display("transmit_change_a: Fail at time %tns",$time());
    transmit_change_c   : cover  property( transmit_change_p    )      ;// $display("transmit_change_c: Pass at time %tns",$time());

    post_tr_change_a    : assert property( post_tr_change_p     ) else $display("post_tr_change_a: Fail at time %tns",$time());
    post_tr_change_c    : cover  property( post_tr_change_p     )      ;// $display("post_tr_change_c: Pass at time %tns",$time());

    wait_change_a       : assert property( wait_change_p        ) else $display("wait_change_a: Fail at time %tns",$time());
    wait_change_c       : cover  property( wait_change_p        )      ;// $display("wait_change_c: Pass at time %tns",$time());
    
endmodule : spi_master

/*
*  File            :   counter_inc_dec_tb.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.17
*  Language        :   SystemVerilog
*  Description     :   This is counter testbench
*  Copyright(c)    :   2019 Vlasov D.V.
*/

module counter_inc_dec_tb();

    parameter           T = 10,
                        rst_delay = 7,
                        start_delay = 200,
                        rep_c = 2000;

    logic   [0 : 0]     clk;
    logic   [0 : 0]     rst_n;
    logic   [0 : 0]     inc;
    logic   [0 : 0]     dec;
    logic   [7 : 0]     cnt;
    logic   [7 : 0]     cnt_w;

    counter_inc_dec
    counter_inc_dec_dut 
    (
        .clk        ( clk       ),
        .rst_n      ( rst_n     ),
        .inc        ( inc       ),
        .dec        ( dec       ),
        .cnt        ( cnt       )
    );

    counter_au
    counter_au_0
    (
        .clk        ( clk       ),
        .rst_n      ( rst_n     ),
        .inc        ( inc       ),
        .dec        ( dec       ),
        .cnt        ( cnt_w     )
    );

    initial
    begin
        #(start_delay);
        clk = '0;
        forever
            #(T/2) clk = !clk;
    end

    initial
    begin
        #(start_delay);
        rst_n = '0;
        repeat(rst_delay) @(posedge clk);
        rst_n = '1;
    end

    initial
    begin
        #(start_delay);
        @(posedge rst_n);
        repeat(rep_c)
        begin
            dec = $urandom_range(0,1);
            inc = $urandom_range(0,1);
            cnt_w = cnt;
            case($urandom_range(0,99))
                0       : cnt_w = $random();
                default : ;
            endcase
            
            @(posedge clk);
        end
        $stop;
    end

endmodule : counter_inc_dec_tb

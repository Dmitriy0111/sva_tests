/*
*  File            :   counter_tb.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.17
*  Language        :   SystemVerilog
*  Description     :   This is simple counter testbench
*  Copyright(c)    :   2019 Vlasov D.V.
*/

module counter_tb();

    parameter           start_delay = 200,
                        T = 10,
                        rst_delay = 7,
                        rep_c = 1000;

    logic   [0 : 0]     clk;
    logic   [0 : 0]     rst_n;
    logic   [7 : 0]     cnt;

    counter
    #(
        .inc_dec    ( '1        )
    )
    counter_dut 
    (
        .clk        ( clk       ),
        .rst_n      ( rst_n     ),
        .cnt        ( cnt       )
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
        repeat(rep_c) 
        begin
            @(posedge clk);
        end
        $stop;
    end

endmodule : counter_tb

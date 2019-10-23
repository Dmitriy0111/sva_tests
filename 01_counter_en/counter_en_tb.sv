/*
*  File            :   counter_en_tb.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.17
*  Language        :   SystemVerilog
*  Description     :   This is simple counter with enable testbench
*  Copyright(c)    :   2019 Vlasov D.V.
*/

module counter_en_tb();

    parameter           T = 10,
                        rst_delay = 7,
                        start_delay = 200,
                        rep_c = 2000;

    logic   [0 : 0]     clk;
    logic   [0 : 0]     rst_n;
    logic   [0 : 0]     en;
    logic   [7 : 0]     cnt;

    counter_en
    #(
        .inc_dec    ( '1        )
    )
    counter_en_dut 
    (
        .clk        ( clk       ),
        .rst_n      ( rst_n     ),
        .en         ( en        ),
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
            en = $urandom_range(0,1);
            @(posedge clk);
        end
        $stop;
    end

endmodule : counter_en_tb

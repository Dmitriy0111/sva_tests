
module counter_inc_dec_tb();

    logic   [0 : 0]     clk;
    logic   [0 : 0]     rst_n;
    logic   [0 : 0]     inc;
    logic   [0 : 0]     dec;
    logic   [7 : 0]     cnt;

    counter_inc_dec
    counter_inc_dec_dut 
    (
        .clk        ( clk       ),
        .rst_n      ( rst_n     ),
        .inc        ( inc       ),
        .dec        ( dec       ),
        .cnt        ( cnt       )
    );

    initial
    begin
        #(20);
        clk = '0;
        forever
            #(5) clk = !clk;
    end

    initial
    begin
        #(20);
        rst_n = '0;
        repeat(7) @(posedge clk);
        rst_n = '1;
    end

    initial
    begin
        repeat(2000)
        begin
            dec = $urandom_range(0,1);
            inc = $urandom_range(0,1);
            @(posedge clk);
        end
        $stop;
    end

endmodule : counter_inc_dec_tb


module counter_en_tb();

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
            en = $urandom_range(0,1);
            @(posedge clk);
        end
        $stop;
    end

endmodule : counter_en_tb

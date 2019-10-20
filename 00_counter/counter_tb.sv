
module counter_tb();

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
            $display("cnt = 0x%h at time = %tns",cnt,$time());
            @(posedge clk);
        end
        $stop;
    end

endmodule : counter_tb

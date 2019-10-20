
module counter_inc_dec_tb();

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
        #(20);
        @(posedge rst_n);
        repeat(2000)
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

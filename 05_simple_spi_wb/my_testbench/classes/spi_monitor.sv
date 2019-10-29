/*
*  File            :   spi_monitor.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.28
*  Language        :   SystemVerilog
*  Description     :   This is spi monitor
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef SPI_MONITOR__SV
`define SPI_MONITOR__SV

class spi_monitor #(parameter ss_width = 1);

    virtual spi_if  #(ss_width)spi_vif;

    string              name = "";
    int                 N = 0;

    logic   [1 : 0]     spi_mode;
    logic   [3 : 0]     spi_clk_div;
    logic   [7 : 0]     rec_data;
    int                 counter;
    int                 counter_pre;

    function new(virtual spi_if #(ss_width) spi_vif, string name = "", int N = 0);
        this.spi_vif = spi_vif;
        this.name = name;
        this.N = N;
    endfunction : new

    task set_spi_mode(logic [1 : 0] spi_mode);
        this.spi_mode = spi_mode;
    endtask : set_spi_mode

    task set_spi_clk_div(logic [3 : 0] spi_clk_div);
        this.spi_clk_div = spi_clk_div;
    endtask : set_spi_clk_div

    task find_counter();
        case( spi_clk_div )
            4'b0000 : counter_pre <= 12'h0;
            4'b0001 : counter_pre <= 12'h1;
            4'b0010 : counter_pre <= 12'h3;
            4'b0011 : counter_pre <= 12'hf;
            4'b0100 : counter_pre <= 12'h1f;
            4'b0101 : counter_pre <= 12'h7;
            4'b0110 : counter_pre <= 12'h3f;
            4'b0111 : counter_pre <= 12'h7f;
            4'b1000 : counter_pre <= 12'hff;
            4'b1001 : counter_pre <= 12'h1ff;
            4'b1010 : counter_pre <= 12'h3ff;
            4'b1011 : counter_pre <= 12'h7ff;
            default : $warning("clock divide not defined");
        endcase
    endtask : find_counter

    task run();
        forever
        begin
            @(negedge spi_vif.ss[N]);
            $display("Monitor %s detect negedge ss signal", name);
            spi_vif.miso_drv[N] = $urandom_range(0,1);
            @(posedge spi_vif.ss[N]);
            spi_vif.miso_drv[N] = 'x;
        end
    endtask : run

endclass : spi_monitor

`endif // SPI_MONITOR__SV

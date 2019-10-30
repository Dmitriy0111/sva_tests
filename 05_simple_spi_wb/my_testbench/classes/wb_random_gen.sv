/*
*  File            :   wb_random_gen.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.28
*  Language        :   SystemVerilog
*  Description     :   This is wishbone random generator
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef WB_RANDOM_GEN__SV
`define WB_RANDOM_GEN__SV

class wb_random_gen;

    rand    logic   [1 : 0]     spi_mode;
    rand    logic   [3 : 0]     spi_clk_div;
    rand    logic   [7 : 0]     spi_tr_data;
    rand    logic   [0 : 0]     spi_ie;
    rand    logic   [2 : 0]     spi_slave_n;

    logic   [2 : 0]     num_spi_slaves = 0;

    logic   [7 : 0]     ss_sel;
    logic   [7 : 0]     spcr;
    logic   [7 : 0]     sper;
    logic   [7 : 0]     tr_data;

    constraint spi_mode_{
        spi_mode inside { [0 : 3] };
    }

    constraint spi_clk_div_{
        spi_clk_div inside { [0:11] };
    }

    constraint spi_tr_data_{
        spi_tr_data inside { [0:255] };
    }

    constraint spi_slave_n_{
        spi_slave_n inside { [0:num_spi_slaves-1] };
    }

    constraint spi_ie_{
        spi_ie inside { ['0:'1] };
    }

    function void post_randomize();
        tr_data = spi_tr_data;
        spcr = { spi_ie , 1'b1 , 1'b0 , 1'b1 , spi_mode , spi_clk_div[1:0] };
        sper = { 6'b000000 , spi_clk_div[3:2] };
        ss_sel = 1'b1 << spi_slave_n;
        $display("Form new transaction:");
        $display("spcr    = 0x%h", spcr);
        $display("cpol    = %b"  , spi_mode[1]);
        $display("cpha    = %b"  , spi_mode[0]);
        $display("sper    = 0x%h", sper);
        $display("clk_div = 0x%h", spi_clk_div);
        $display("tx_data = 0x%h", tr_data);
        $display("ss_sel  = 0b%b", ss_sel);
    endfunction : post_randomize

    function new();
    endfunction : new

    task set_num_spi_slaves(logic [2 : 0] num_spi_slaves);
        this.num_spi_slaves = num_spi_slaves;
    endtask : set_num_spi_slaves

endclass : wb_random_gen

`endif // WB_RANDOM_GEN__SV

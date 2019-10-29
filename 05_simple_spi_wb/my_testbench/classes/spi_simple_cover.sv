/*
*  File            :   spi_simple_cover.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.10.28
*  Language        :   SystemVerilog
*  Description     :   This is spi_simple cover class 
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef SPI_SIMPLE_COVER__SV
`define SPI_SIMPLE_COVER__SV

class spi_simple_cover;

    virtual wb_if       wb_vif;

    logic   [7 : 0]     spcr;
    logic   [7 : 0]     sper;

    covergroup spi_simple_cg;

        clk_div_cp : coverpoint { sper[1:0] , spcr[1:0] }
        {
            bins cd_2       = { 4'b0000 };
            bins cd_4       = { 4'b0001 };
            bins cd_8       = { 4'b0100 };
            bins cd_16      = { 4'b0010 };
            bins cd_32      = { 4'b0011 };
            bins cd_64      = { 4'b0101 };
            bins cd_128     = { 4'b0110 };
            bins cd_256     = { 4'b0111 };
            bins cd_512     = { 4'b1000 };
            bins cd_1024    = { 4'b1001 };
            bins cd_2048    = { 4'b1010 };
            bins cd_4096    = { 4'b1011 };
            illegal_bins ib = { [12 : 15] };
        }

        spi_mode_cp : coverpoint { spcr[3] , spcr[2]} // CPOL CPHA
        {
            bins mode_0     = { 2'b00 };
            bins mode_1     = { 2'b01 };
            bins mode_2     = { 2'b10 };
            bins mode_3     = { 2'b11 };
        }

        ie_cp : coverpoint spcr[7] // interrupt enable
        {
            bins ie     = { '1 };
            bins ine    = { '0 };
        }

        clk_div_spi_mode_cross : cross clk_div_cp, spi_mode_cp;

    endgroup : spi_simple_cg

    function new(virtual wb_if wb_vif);
        this.wb_vif = wb_vif;
        spi_simple_cg = new();
    endfunction : new

    task run();
        @(posedge wb_vif.RST);
        forever
        begin
            @(posedge wb_vif.CLK);
            if( &{ wb_vif.WE , wb_vif.STB , wb_vif.CYC } )
            case( wb_vif.ADR )
                3'b000  : spcr = wb_vif.DATA_O;
                3'b011  : sper = wb_vif.DATA_O;
                3'b010  : spi_simple_cg.sample();
            endcase
        end
    endtask : run

endclass : spi_simple_cover

`endif // SPI_SIMPLE_COVER__SV

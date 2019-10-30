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
    logic   [7 : 0]     shift_reg;

    function new(virtual spi_if #(ss_width) spi_vif, string name = "", int N = 0);
        this.spi_vif = spi_vif;
        this.name = name;
        this.N = N;
    endfunction : new

    task set_spi_mode(logic [1 : 0] spi_mode);
        this.spi_mode = spi_mode;
    endtask : set_spi_mode

    task run(ref logic [7 : 0] mon_tx_data[$], ref logic [7 : 0] mon_rx_data[$]);
        forever
        begin
            @(negedge spi_vif.ss[N]);
            shift_reg = $urandom_range(0,255);
            $display("%s random tx data = 0x%h",name,shift_reg);
            mon_tx_data.push_back(shift_reg);
            $display("%s detect negedge ss signal", name);
            repeat(8)
            begin
                if( spi_mode[0] == '0)
                begin
                    spi_vif.miso_drv[N] = shift_reg[7];
                    if( spi_mode[1] == '0 )
                        @(posedge spi_vif.sck);
                    else
                        @(negedge spi_vif.sck);
                    shift_reg = { shift_reg , spi_vif.mosi };
                    if( spi_mode[1] == '0 )
                        @(negedge spi_vif.sck);
                    else
                        @(posedge spi_vif.sck);
                end
                else
                begin
                    if( spi_mode[1] == '0 )
                        @(posedge spi_vif.sck);
                    else
                        @(negedge spi_vif.sck);
                    spi_vif.miso_drv[N] = shift_reg[7];
                    if( spi_mode[1] == '0 )
                        @(negedge spi_vif.sck);
                    else
                        @(posedge spi_vif.sck);
                    shift_reg = { shift_reg , spi_vif.mosi };
                end
            end
            mon_rx_data.push_back(shift_reg);
            @(posedge spi_vif.ss[N]);
            $display("%s receive data = 0x%h",name,shift_reg);
            spi_vif.miso_drv[N] = 'x;
        end
    endtask : run

endclass : spi_monitor

`endif // SPI_MONITOR__SV

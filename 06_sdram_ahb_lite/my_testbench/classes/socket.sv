/*
*  File            :   socket.sv
*  Autor           :   Vlasov D.V.
*  Data            :   2019.11.05
*  Language        :   SystemVerilog
*  Description     :   This is socket
*  Copyright(c)    :   2019 Vlasov D.V.
*/

`ifndef SOCKET__SV
`define SOCKET__SV

class socket #(type mail_type=int);

    event                   side_e[];
    mailbox #(mail_type)    side_m[];

    function new(int side_n);
        side_e = new[side_n];
        side_m = new[side_n];
        foreach(side_m[i])
            side_m[i] = new();
    endfunction : new

    task set_msg(int sock_index, mail_type msg);
        side_m[sock_index].put(msg);
    endtask : set_msg

    task trig_side(int sock_index);
        -> side_e[sock_index];
    endtask : trig_side

    task send_msg(int sock_index, mail_type msg);
        this.set_msg(sock_index,msg);
        this.trig_side(sock_index);
    endtask : send_msg

    task wait_side(int sock_index);
        @(side_e[sock_index]);
    endtask : wait_side

    task get_msg(int sock_index, ref mail_type msg);
        side_m[sock_index].get(msg);
    endtask : get_msg

    task rec_msg(int sock_index, ref mail_type msg);
        this.wait_side(sock_index);
        this.get_msg(sock_index,msg);
    endtask : rec_msg

endclass : socket

`endif // SOCKET__SV

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

    event                   side_e;
    mailbox #(mail_type)    side_m;

    extern function new();
    extern task     set_msg(mail_type msg);
    extern task     trig_side();
    extern task     connect(socket #(mail_type) other_sock);
    extern task     send_msg(mail_type msg);
    extern task     wait_side();
    extern task     get_msg(ref mail_type msg);
    extern task     rec_msg(ref mail_type msg);

endclass : socket

function socket::new();
    side_m = new();
endfunction : new

task socket::set_msg(mail_type msg);
    side_m.put(msg);
endtask : set_msg

task socket::trig_side();
    -> side_e;
endtask : trig_side

task socket::connect(socket #(mail_type) other_sock);
    side_e = other_sock.side_e;
    side_m = other_sock.side_m;
endtask : connect

task socket::send_msg(mail_type msg);
    this.set_msg(msg);
    this.trig_side();
endtask : send_msg

task socket::wait_side();
    @(side_e);
endtask : wait_side

task socket::get_msg(ref mail_type msg);
    side_m.get(msg);
endtask : get_msg

task socket::rec_msg(ref mail_type msg);
    this.wait_side();
    this.get_msg(msg);
endtask : rec_msg

`endif // SOCKET__SV

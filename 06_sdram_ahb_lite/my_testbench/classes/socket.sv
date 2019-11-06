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

    extern function new(int side_n);
    extern task     set_msg(int sock_index, mail_type msg);
    extern task     trig_side(int sock_index);
    extern task     connect(socket #(mail_type) other_sock);
    extern task     send_msg(int sock_index, mail_type msg);
    extern task     wait_side(int sock_index);
    extern task     get_msg(int sock_index, ref mail_type msg);
    extern task     rec_msg(int sock_index, ref mail_type msg);

endclass : socket

function socket::new(int side_n);
    side_e = new[side_n];
    side_m = new[side_n];
    foreach(side_m[i])
        side_m[i] = new();
endfunction : new

task socket::set_msg(int sock_index, mail_type msg);
    side_m[sock_index].put(msg);
endtask : set_msg

task socket::trig_side(int sock_index);
    -> side_e[sock_index];
endtask : trig_side

task socket::connect(socket #(mail_type) other_sock);
    if( side_e.size() != other_sock.side_e.size() )
        $fatal("Sock connect error!");
    foreach( side_e[i] )
        side_e[i] = other_sock.side_e[i];
    foreach( side_m[i] )
        side_m[i] = other_sock.side_m[i];
endtask : connect

task socket::send_msg(int sock_index, mail_type msg);
    this.set_msg(sock_index,msg);
    this.trig_side(sock_index);
endtask : send_msg

task socket::wait_side(int sock_index);
    @(side_e[sock_index]);
endtask : wait_side

task socket::get_msg(int sock_index, ref mail_type msg);
    side_m[sock_index].get(msg);
endtask : get_msg

task socket::rec_msg(int sock_index, ref mail_type msg);
    this.wait_side(sock_index);
    this.get_msg(sock_index,msg);
endtask : rec_msg

`endif // SOCKET__SV

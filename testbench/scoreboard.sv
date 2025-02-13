//=====================================================================
// Description:
// This file realize the scoreboard
// Designer : lynnxie@sjtu.edu.cn
// Revision History:
// V0 data:2024/11/24 Initial version, extraordinary.h@sjtu.edu.cn
//=====================================================================

`timescale 1ns/1ps

package scoreboard_pkg;

    import objects_pkg::*;

    class scoreboard;
        
        // BUILD
        //=============================================================
        int total_cases;
        int mismatched;        // the number of cases which are error

        logic [63:0] masked_data1;
        logic [63:0] masked_data2;
        logic [63:0] key;
        logic [31:0] ctrl_packet;
        logic [31:0] data_packet;
        logic        write_g;
        logic [5:0]  sel_g;
        logic [31:0] addr_g;
        logic [31:0] wdata_g;
        logic [63:0] rdata_g;
        
        logic [5:0] sel_queue [$];

        mailbox #(icb_trans) icb2sb;
        mailbox #(apb_trans) apb2sb0;
        mailbox #(apb_trans) apb2sb1;
        mailbox #(apb_trans) apb2sb2;
        mailbox #(apb_trans) apb2sb3; 

        function new(
            mailbox #(icb_trans) icb2sb,
            mailbox #(apb_trans) apb2sb0,
            mailbox #(apb_trans) apb2sb1,
            mailbox #(apb_trans) apb2sb2,
            mailbox #(apb_trans) apb2sb3
        );
            this.icb2sb = icb2sb;
            this.apb2sb0 = apb2sb0;
            this.apb2sb1 = apb2sb1;
            this.apb2sb2 = apb2sb2;
            this.apb2sb3 = apb2sb3;
        endfunction //new

        // FUNC : compare ICB and APB transactions
        //=============================================================
        task automatic compare();
            localparam  CTRL_ADDR = 32'h2000_0000;
            localparam  STAT_ADDR = 32'h2000_0008;
            localparam  WDATA_ADDR = 32'h2000_0010;
            localparam  RDATA_ADDR = 32'h2000_0018;
            localparam  KEY_ADDR = 32'h2000_0020;

            localparam  S0 = 6'b000001;
            localparam  S1 = 6'b000010;
            localparam  S2 = 6'b000100;
            localparam  S3 = 6'b001000;

            icb_trans icb_mon1;
            icb_trans icb_mon2;
            apb_trans apb_mon;

            $display("[TB- SBD ] Scoreboard Compare Program Begin !");

            forever begin
                this.icb2sb.get(icb_mon1); 
                // $display("sample READ from icb = %h", icb_mon1.read);

                if(~icb_mon1.read) // if icb is write
                begin
                    // $display("sample wdata from icb = %h", icb_mon1.wdata);
                    for (int i = 0; i < 8; i++)  // get the data after mask
                    begin
                        masked_data1[i*8 +: 8] = icb_mon1.wdata[i*8 +: 8] & {8{~icb_mon1.mask[i]}};
                    end

                    if(icb_mon1.addr == KEY_ADDR)  // write the key reg
                        key = masked_data1;
                    else if(icb_mon1.addr == WDATA_ADDR) // write wdata to apb, maybe write apb or read apb
                    begin
                        
                        ctrl_packet = key ^ masked_data1;  // decrypt
                        
                        if(ctrl_packet[0] == 0)    // decode
                        begin
                            write_g = ctrl_packet[1];
                            addr_g = ctrl_packet[31:8];
                            sel_g = ctrl_packet[7:2];
                            
                            if(sel_g == S0 || sel_g == S1 || sel_g == S2 || sel_g == S3)
                            begin
                                sel_queue.push_back(sel_g);

                                this.icb2sb.get(icb_mon2); // apb write: data packet
                                                           // apb read: empty packet
                            
                                if (ctrl_packet[1] == 1)  // if apb is write
                                begin

                                    case (sel_queue.pop_front()) // get the data from the mailbox of apb agent
                                        S0: this.apb2sb0.get(apb_mon);
                                        S1: this.apb2sb1.get(apb_mon);
                                        S2: this.apb2sb2.get(apb_mon);
                                        S3: this.apb2sb3.get(apb_mon);
                                    default: $display("[TB- SBD ] APB slave selection signal error!");
                                    endcase

                                    total_cases += 1;
                                    for (int i = 0; i < 8; i++)  // get the data after mask
                                    begin
                                        masked_data2[i*8 +: 8] = icb_mon2.wdata[i*8 +: 8] & {8{~icb_mon2.mask[i]}};
                                    end

                                    data_packet = key ^ masked_data2;

                                    wdata_g = data_packet[31:1];

                                    if(wdata_g == apb_mon.wdata && addr_g == apb_mon.addr && 
                                    write_g == apb_mon.write)
                                    begin
                                        $display("[TB- SBD ] Test case %0d (write) pass!", total_cases);
                                        $display("[TB- SBD ] Now error rate: %.2f%%", real'(mismatched) / total_cases * 100);
                                    end
                                    else 
                                    begin
                                        mismatched += 1;
                                        if(wdata_g != apb_mon.wdata)
                                            $display("[TB- SBD ] Test case %0d (write) fail, pwdata wrong!", total_cases);
                                        if(addr_g != apb_mon.addr)
                                            $display("[TB- SBD ] Test case %0d (write) fail, paddr wrong!", total_cases);
                                        if(write_g != apb_mon.write)
                                            $display("[TB- SBD ] Test case %0d (write) fail, pwrite wrong!", total_cases);
                                        $display("[TB- SBD ] Now error rate: %.2f%%", real'(mismatched) / total_cases * 100);
                                    end
                                end
                            end
                            else
                            begin
                                total_cases += 1;
                                mismatched +=1;
                                $display("[TB- SBD ] Test case %0d (ctrl) fail, psel wrong!", total_cases);
                                $display("[TB- SBD ] Now error rate: %.2f%%", real'(mismatched) / total_cases * 100);
                            end
                        end
                    end
                end
                else   // if is icb read
                begin
                    // $display("sample rdata from icb = %h", icb_mon1.rdata);
                    // $display("sample RADDR from icb = %h", icb_mon1.addr);
                    if(icb_mon1.addr == RDATA_ADDR)
                    begin
                        case (sel_queue.pop_front()) // get the data from the mailbox of apb agent
                            S0: this.apb2sb0.get(apb_mon);
                            S1: this.apb2sb1.get(apb_mon);
                            S2: this.apb2sb2.get(apb_mon);
                            S3: this.apb2sb3.get(apb_mon);
                            default: $display("[TB- SBD ] APB slave selection signal error!");
                        endcase
                        
                        total_cases += 1;
                        
                        rdata_g = {32'b0, apb_mon.rdata ^ key}; // encrypt
                        // $display("-----------------------------rdata_golden = %h", rdata_g);

                        if(rdata_g == icb_mon1.rdata)
                        begin
                            $display("[TB- SBD ] Test case %0d (read) pass!", total_cases);
                            $display("[TB- SBD ] Now error rate: %.2f%%", real'(mismatched) / total_cases * 100);
                        end
                        else
                        begin
                            mismatched += 1;
                            $display("[TB- SBD ] Test case %0d (read) fail, prdata wrong!", total_cases);
                            $display("[TB- SBD ] Now error rate: %.2f%%", real'(mismatched) / total_cases * 100);
                        end
                    end
                end
            end

        endtask

    endclass
endpackage
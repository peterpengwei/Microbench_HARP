// Copyright (c) 2013-2015, Intel Corporation
//
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
//
// * Redistributions of source code must retain the above copyright notice,
// this list of conditions and the following disclaimer.
// * Redistributions in binary form must reproduce the above copyright notice,
// this list of conditions and the following disclaimer in the documentation
// and/or other materials provided with the distribution.
// * Neither the name of Intel Corporation nor the names of its contributors
// may be used to endorse or promote products derived from this software
// without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
// IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE
// LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR
// CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF
// SUBSTITUTE GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
// INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN
// CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.


module spl_trn(
    input  wire                             clk,
    input  wire                             reset_n,
    input  wire                             linkup,
        
    // TRN TX
    input  wire                             trn_tcfg_req_n,        
    input  wire [5:0]                       trn_tbuf_av,
    input  wire                             trn_terr_drop_n,
    input  wire                             trn_tdst_rdy_n,  
    output reg  [63:0]                      trn_td,
    output reg                              trn_trem_n,
    output reg                              trn_tsof_n,
    output reg                              trn_teof_n,
    output reg                              trn_tsrc_rdy_n,
    output reg                              trn_terrfwd_n,
    output reg                              trn_tcfg_gnt_n,
    output reg                              trn_tstr_n, 
    output reg                              trn_tsrc_dsc_n,  
         
    // TRN Rx
    input  wire [63:0]                      trn_rd,
    input  wire                             trn_rrem_n,
    input  wire                             trn_rsof_n,
    input  wire                             trn_reof_n,
    input  wire                             trn_rsrc_rdy_n,
    input  wire                             trn_rsrc_dsc_n,
    input  wire                             trn_rerrfwd_n,
    input  wire [6:0]                       trn_rbar_hit_n,
    output wire                             trn_rdst_rdy_n,
    output wire                             trn_rnp_ok_n,
                
    // cfg interface
    input  wire [7:0]                       cfg_bus_number,
    input  wire [4:0]                       cfg_device_number,
    input  wire [2:0]                       cfg_function_number,
//    input  wire [10:0]                      io_max_payload                 // the max payload of an io packet in DW
                    
    // spl_io-->spl_csr, RX CSR SWW
    input  wire                             csr_reset,  
    input  wire                             csr_enable,  
    output reg                              io_rx_csr_valid,
    output reg  [13:0]                      io_rx_csr_addr,
    output reg  [31:0]                      io_rx_csr_data,  
    
    // spl_io-->spl_core, RX RD    
    output reg                              io_rx_rd_valid,
    output reg  [13:0]                      io_rx_rd_tag   /* synthesis syn_preserve=1 */,
    output reg  [511:0]                     io_rx_data,
            
    // spl_io-->spl_core, RX WR    
    output reg                              io_rx_wr_valid,    
    output reg  [17:0]                      io_rx_wr_hdr    /* synthesis syn_preserve=1 */,
                
    // spl_core --> spl_io, TX read request
    output reg                              io_trq_re,
    input  wire [`SPL_TRQ_WIDTH-1:0]        cor_trq_dout,
    input  wire                             cor_trq_empty,
    input  wire                             cor_trq_almostempty,
        
    // spl_core --> spl_io, TX write request
    output reg                              io_twq_re,
    input  wire [`SPL_TWQ_WIDTH-1:0]        cor_twq_dout,
    input  wire                             cor_twq_empty,
    input  wire                             cor_twq_almostempty,
    
    output reg                              trn_rx_fmttype_err,
    output reg                              trn_terr_drop,
    output reg                              trn_tbuf_err,
    output reg                              trn_rx_data_err
);
    

    localparam [1:0]        
        TWQ_RD_STATE_IDLE       = 2'b00,
        TWQ_RD_STATE_RD         = 2'b01,        
        TWQ_RD_STATE_VALID      = 2'b10,
        TWQ_RD_STATE_WAIT       = 2'b11;
                 
    localparam [3:0] 
        TRN_TX_STATE_IDLE       = 4'h0,
        TRN_TX_STATE_SOF        = 4'h1,
        TRN_TX_STATE_ADDR       = 4'h2,
        TRN_TX_STATE_DATA0      = 4'h3,                
        TRN_TX_STATE_DATA1      = 4'h4,
        TRN_TX_STATE_DATA2      = 4'h5,
        TRN_TX_STATE_DATA3      = 4'h6,
        TRN_TX_STATE_DATA4      = 4'h7,
        TRN_TX_STATE_DATA5      = 4'h8,
        TRN_TX_STATE_DATA6      = 4'h9,
        TRN_TX_STATE_WR_CONT    = 4'ha;
                                       
    localparam [3:0] 
        TRN_RX_STATE_IDLE           = 4'h0,
        TRN_RX_STATE_MW32           = 4'h1,
        TRN_RX_STATE_MW64_ADDR      = 4'h2,
        TRN_RX_STATE_MW64_DATA      = 4'h3,
        TRN_RX_STATE_CPLD           = 4'h4,
        TRN_RX_STATE_CPLD_DATA0     = 4'h5,                
        TRN_RX_STATE_CPLD_DATA1     = 4'h6,
        TRN_RX_STATE_CPLD_DATA2     = 4'h7,
        TRN_RX_STATE_CPLD_DATA3     = 4'h8,
        TRN_RX_STATE_CPLD_DATA4     = 4'h9,
        TRN_RX_STATE_CPLD_DATA5     = 4'ha,
        TRN_RX_STATE_CPLD_DATA6     = 4'hb,
        TRN_RX_STATE_CPLD_DATA7     = 4'hc;
                                                                                
    
    wire [511:0]                    cor_twq_dout_data;
    wire [31:0]                     cor_twq_dout_addr;    
    wire                            cor_twq_dout_addr_64;   
             
    wire [1:0]                      cor_twq_dout_cmd;
    wire [13:0]                     cor_twq_dout_tag;
    wire [5:0]                      cor_twq_dout_len;
        
    reg                             tw_req;
    reg  [31:0]                     tw_addr;
    reg                             tw_addr_64;
    reg  [511:0]                    tw_data;
    reg  [5:0]                      tw_len;
    reg  [13:0]                     tw_tag;
    reg                             tw_grant;
    reg  [1:0]                      twq_rd_state;
    
    wire [`SPL_TAG_WIDTH-1:0]       cor_trq_dout_tag;
    wire [5:0]                      cor_trq_dout_len;    
    wire [31:0]                     cor_trq_dout_addr;
        
    reg                             io_trq_re_d1;
            
    wire                            tr_req;
    wire [31:0]                     tr_addr;
    wire [4:0]                      tr_tag;
    reg  [1:0]                      tr_req_pend;
    reg  [1:0]                      tr_req_cnt;        
    reg  [1:0]                      tr_addr_64_pend;
        
    (* ram_extract = "no" *) reg  [31:0]                     tr_addr_pend[0:1];
    (* ram_extract = "no" *) reg  [`SPL_TAG_WIDTH-1:0]       tr_tag_pend[0:1];
    (* ram_extract = "no" *) reg  [5:0]                      tr_len_pend[0:1];
    
    reg                             tr_wi;
    reg                             tr_ri;
    
    reg                             tr_grant;
    reg                             tr_grant_last;
    wire [9:0]                      tr_len;
    
    wire [31:0]                     pcie_hdr1_wr;  
    wire [31:0]                     pcie_hdr1_rd;     

    reg  [31:0]                     trn_addr;
    reg                             trn_addr_64;
    reg  [511:0]                    trn_data;
    reg  [5:0]                      trn_len;
    
    reg  [3:0]                      trn_tx_state;
    reg                             trn_tw_wait;

    reg  [10:0]                     rr_len;
    reg  [31:0]                     rr_1st_dw;
    reg                             rr_split;
    
    reg  [3:0]                      trn_rx_state;
    wire [7:0]                      trn_rd_tag;
    wire [9:0]                      trn_rd_len;
    reg                             trn_rdst_rdy;
                           
                                       
    //-------------------------------------------------------------------------------------
    // read TX_WR transmit queue every 10 or 8 cycles
    //-------------------------------------------------------------------------------------
    // data(512) + len(6) + cmd(2) + addr(32) +tag(14) = 566
    assign cor_twq_dout_data = cor_twq_dout[565:54];
    assign cor_twq_dout_len = cor_twq_dout[53:48];
    assign cor_twq_dout_cmd = cor_twq_dout[47:46];
    assign cor_twq_dout_addr = cor_twq_dout[45:14];
    assign cor_twq_dout_addr_64 = (cor_twq_dout[45:40] != 6'b0);
    assign cor_twq_dout_tag = cor_twq_dout[13:0];
        
    always @(posedge clk) begin
        if (~reset_n | csr_reset) begin
            io_twq_re <= 1'b0;
            tw_req <= 1'b0;
            twq_rd_state <= TWQ_RD_STATE_IDLE;
        end

        else begin
            io_twq_re <= 1'b0;        

            case (twq_rd_state)
                TWQ_RD_STATE_IDLE : begin
                    if (~cor_twq_empty) begin
                        io_twq_re <= 1'b1;                         
                        twq_rd_state <= TWQ_RD_STATE_RD;
                    end
                end
            
                TWQ_RD_STATE_RD : begin
                    twq_rd_state <= TWQ_RD_STATE_VALID;
                end
                  
                TWQ_RD_STATE_VALID : begin
                    tw_addr <= cor_twq_dout_addr;
                    tw_addr_64 <= cor_twq_dout_addr_64;
                    tw_data <= cor_twq_dout_data;                    
                    tw_tag <= cor_twq_dout_tag;
                    tw_len <= cor_twq_dout_len;
                    
                    if (cor_twq_dout_cmd != `COR_REQ_WR_FENCE) begin
                        tw_req <= 1'b1;
                        twq_rd_state <= TWQ_RD_STATE_WAIT;
                    end
                    else begin
                        twq_rd_state <= TWQ_RD_STATE_IDLE;
                    end
                end
                
                TWQ_RD_STATE_WAIT : begin
                    if (tw_grant) begin
                        tw_req <= 1'b0;
                        twq_rd_state <= TWQ_RD_STATE_IDLE;
                    end              
                end                                            
            endcase          
        end
    end
    
        
    //-------------------------------------------------------------------------------------
    // read TX_RD transmit queue every 2 cycles
    //-------------------------------------------------------------------------------------  
    // addr(32) + len(6) + `SPL_TAG_WIDTH    
    assign cor_trq_dout_addr = cor_trq_dout[`SPL_TAG_WIDTH+37:`SPL_TAG_WIDTH+6];
    assign cor_trq_dout_len = cor_trq_dout[`SPL_TAG_WIDTH+5:`SPL_TAG_WIDTH];
    assign cor_trq_dout_tag = cor_trq_dout[`SPL_TAG_WIDTH-1:0];
                               
    assign tr_req = tr_req_pend[tr_ri];
    assign tr_addr = tr_addr_pend[tr_ri];
    assign tr_addr_64 = tr_addr_64_pend[tr_ri];
    assign tr_tag = tr_tag_pend[tr_ri];
    assign tr_len = {tr_len_pend[tr_ri], 4'b0};
    
                                              
    always @(posedge clk) begin
        if ((~reset_n) | csr_reset) begin
            tr_req_pend <= 2'b0;
            io_trq_re <= 1'b0;
            io_trq_re_d1 <= 1'b0;
            tr_req_cnt <= 2'b0;
            tr_ri <= 1'b0;
            tr_wi <= 1'b0;
        end

        else begin
            io_trq_re <= 1'b0;                         
            io_trq_re_d1 <= io_trq_re; 

            // read trq every other cycle
            if ((~cor_trq_empty) & (~io_trq_re) & (tr_req_cnt < 2'h2)) begin
                io_trq_re <= 1'b1; 
            end

            // buffer and drive tr_req
            if (io_trq_re_d1) begin
                tr_req_pend[tr_wi] <= 1'b1;
                tr_addr_pend[tr_wi] <= cor_trq_dout_addr;
                tr_addr_64_pend[tr_wi] <= (cor_trq_dout_addr[31:26] != 6'b0);
                tr_tag_pend[tr_wi] <= cor_trq_dout_tag;
                tr_len_pend[tr_wi] <= cor_trq_dout_len; 
                tr_wi <= ~tr_wi;
            end                                

            // clear tr_reg
            if (tr_grant) begin
                tr_req_pend[tr_ri] <= 1'b0;
                tr_ri <= ~tr_ri;

                // synthesis translate_off
                assert ((tr_req_cnt > 0) & tr_req)else $fatal("received tr_grant while no pending tr_req");
                // synthesis translate_on                          
            end            
                        
            // update tr_req_cnt
            case ({io_trq_re, tr_grant})
                2'b10 : tr_req_cnt <= tr_req_cnt + 1'b1;
                2'b01 : tr_req_cnt <= tr_req_cnt - 1'b1;
            endcase
        end
    end
    

    //------------------------------------------------------
    // arbitrate TX_WR, TX_RD, and drive TRN_TX
    //------------------------------------------------------
    assign pcie_hdr1_wr = {cfg_bus_number, cfg_device_number, cfg_function_number, 8'b0, 8'hff};
    assign pcie_hdr1_rd = {cfg_bus_number, cfg_device_number, cfg_function_number, 3'b0, tr_tag, 8'hff};    
                
    always @(posedge clk) begin
        if ((~reset_n) | csr_reset) begin
            tw_grant <= 1'b0;
            tr_grant <= 1'b0;
            tr_grant_last <= 1'b0;
            
            trn_tsrc_rdy_n <= 1'b1;
            trn_tsof_n <= 1'b1;
            trn_teof_n <= 1'b1;
            trn_trem_n <= 1'b1;            

            trn_terrfwd_n <= 1'b1; 
            trn_tcfg_gnt_n <= 1'b0; 
            trn_tstr_n <= 1'b1; 
            trn_tsrc_dsc_n <= 1'b1;
            
            io_rx_wr_valid <= 1'b0;
            
            trn_tx_state <= TRN_TX_STATE_IDLE;
        end

        else begin
            tw_grant <= 1'b0;        
            tr_grant <= 1'b0;     
            io_rx_wr_valid <= 1'b0;
                        
            case (trn_tx_state)
                TRN_TX_STATE_IDLE : begin
                    // arbitrate TW, TR, drive SOF
                    if (trn_teof_n | ((~trn_teof_n) & (~trn_tdst_rdy_n))) begin
                        trn_teof_n <= 1'b1;
                        trn_trem_n <= 1'b1;
                        
                        case ({tr_grant_last, tr_req, tw_req})
                            3'b101,
                            3'b111,
                            3'b001 : begin  // choose TW
                                tw_grant <= 1'b1;
                                tr_grant_last <= 1'b0;
                                trn_addr <= tw_addr;    //{26'b0, tw_addr, 6'b0};
                                trn_addr_64 <= tw_addr_64;
                                trn_data <= tw_data;
                                trn_len <= tw_len;
                                
                                trn_tsrc_rdy_n <= 1'b0;
                                trn_tsof_n <= 1'b0; 
                                
                                if (tw_addr_64) begin
                                    trn_td <= {1'b0, `PCIE_FMTTYPE_MEM_WRITE64, 14'b0, tw_len, 4'b0, pcie_hdr1_wr};     
                                end
                                else begin
                                    trn_td <= {1'b0, `PCIE_FMTTYPE_MEM_WRITE32, 14'b0, tw_len, 4'b0, pcie_hdr1_wr}; 
                                end

                                // fake RX_WR
                                io_rx_wr_valid <= 1'b1;
                                io_rx_wr_hdr <= {`CCI_RSP_WR, tw_tag};
                                
                                trn_tx_state <= TRN_TX_STATE_SOF;                                              
                            end

                            3'b110,
                            3'b010,
                            3'b011 : begin // choose TR
                                tr_grant <= 1'b1;
                                tr_grant_last <= 1'b1;  
                                trn_addr <= tr_addr;    //{26'b0, tr_addr, 6'b0};  
                                trn_addr_64 <= tr_addr_64;
                                
                                trn_tsrc_rdy_n <= 1'b0;
                                trn_tsof_n <= 1'b0; 
                                
                                if (tr_addr_64) begin
                                    trn_td <= {1'b0, `PCIE_FMTTYPE_MEM_READ64, 14'b0, tr_len, pcie_hdr1_rd};
                                end
                                else begin
                                    trn_td <= {1'b0, `PCIE_FMTTYPE_MEM_READ32, 14'b0, tr_len, pcie_hdr1_rd};
                                end

                                trn_tx_state <= TRN_TX_STATE_SOF; 
                            end

                            default : begin
                                // no request pending
                                trn_tsrc_rdy_n <= 1'b1;   
                                tr_grant_last <= 1'b0;                             
                            end
                        endcase
                    end
                end
                
                TRN_TX_STATE_SOF : begin
                    // observed SOF, drive address
                    if (~trn_tdst_rdy_n) begin
                        trn_tsof_n <= 1'b1;  
                        
                        if (trn_addr_64) begin                       
                            trn_td <= {26'b0, trn_addr, 6'b0};
                        end
                        else begin
                            trn_td <= {trn_addr[25:0], 6'b0, trn_data[7:0], trn_data[15:8], trn_data[23:16], trn_data[31:24]};
                        end

                        if (tr_grant_last) begin    // for read, EOF
                            trn_teof_n <= 1'b0; 
                            trn_tx_state <= TRN_TX_STATE_IDLE;   
                            
                            if (trn_addr_64)                               
                                trn_trem_n <= 1'b0;
                            else
                                trn_trem_n <= 1'b1;
                        end
                        else begin
                            trn_tx_state <= TRN_TX_STATE_ADDR;
                        end
                    end
                end
                
                TRN_TX_STATE_ADDR : begin
                    // observed address, drive 1st data
                    if (~trn_tdst_rdy_n) begin
                        if (trn_addr_64) begin
                            trn_td <= { trn_data[7:0], trn_data[15:8],trn_data[23:16], trn_data[31:24],
                                        trn_data[39:32], trn_data[47:40],trn_data[55:48], trn_data[63:56]
                                      };
                        end
                        else begin
                            trn_td <= { trn_data[39:32], trn_data[47:40],trn_data[55:48], trn_data[63:56],
                                        trn_data[71:64], trn_data[79:72], trn_data[87:80], trn_data[95:88]
                                      };                        
                        end

                        trn_tx_state <= TRN_TX_STATE_DATA0;                                              
                    end
                end                
                
                TRN_TX_STATE_DATA0 : begin
                    // observed address, drive 1st 8 bytes of data
                    if (~trn_tdst_rdy_n) begin                    
                        if (trn_addr_64) begin
                            trn_td <= { trn_data[71:64], trn_data[79:72], trn_data[87:80], trn_data[95:88],
                                        trn_data[103:96], trn_data[111:104], trn_data[119:112], trn_data[127:120]
                                      };
                        end
                        else begin
                            trn_td <= { trn_data[103:96], trn_data[111:104], trn_data[119:112], trn_data[127:120],
                                        trn_data[135:128], trn_data[143:136], trn_data[151:144], trn_data[159:152]
                                      };                        
                        end                                  
                        trn_tx_state <= TRN_TX_STATE_DATA1;                                              
                    end
                end                  
                
                TRN_TX_STATE_DATA1 : begin
                    if (~trn_tdst_rdy_n) begin
                        if (trn_addr_64) begin
                            trn_td <= { trn_data[135:128], trn_data[143:136], trn_data[151:144], trn_data[159:152],
                                        trn_data[167:160], trn_data[175:168], trn_data[183:176], trn_data[191:184]
                                      };
                        end
                        else begin
                            trn_td <= { trn_data[167:160], trn_data[175:168], trn_data[183:176], trn_data[191:184],
                                        trn_data[199:192], trn_data[207:200], trn_data[215:208], trn_data[223:216]
                                      };                        
                        end                                  
                        trn_tx_state <= TRN_TX_STATE_DATA2;                                              
                    end
                end                            
                
                TRN_TX_STATE_DATA2 : begin
                    if (~trn_tdst_rdy_n) begin
                        if (trn_addr_64) begin
                            trn_td <= { trn_data[199:192], trn_data[207:200], trn_data[215:208], trn_data[223:216],
                                        trn_data[231:224], trn_data[239:232], trn_data[247:240], trn_data[255:248]
                                      };
                        end
                        else begin
                            trn_td <= { trn_data[231:224], trn_data[239:232], trn_data[247:240], trn_data[255:248],
                                        trn_data[263:256], trn_data[271:264],trn_data[279:272], trn_data[287:280]
                                      };                        
                        end
                        trn_tx_state <= TRN_TX_STATE_DATA3;                                              
                    end
                end           
                                
                TRN_TX_STATE_DATA3 : begin
                    if (~trn_tdst_rdy_n) begin
                        if (trn_addr_64) begin
                            trn_td <= { trn_data[263:256], trn_data[271:264],trn_data[279:272], trn_data[287:280],
                                        trn_data[295:288], trn_data[303:296],trn_data[311:304], trn_data[319:312]
                                      };
                        end
                        else begin
                            trn_td <= { trn_data[295:288], trn_data[303:296],trn_data[311:304], trn_data[319:312],
                                        trn_data[327:320], trn_data[335:328], trn_data[343:336], trn_data[351:344]
                                      };                        
                        end
                        trn_tx_state <= TRN_TX_STATE_DATA4;                                              
                    end
                end                
                
                TRN_TX_STATE_DATA4 : begin
                    if (~trn_tdst_rdy_n) begin
                        if (trn_addr_64) begin
                            trn_td <= { trn_data[327:320], trn_data[335:328], trn_data[343:336], trn_data[351:344],
                                        trn_data[359:352], trn_data[367:360], trn_data[375:368], trn_data[383:376]
                                      };
                        end
                        else begin
                            trn_td <= { trn_data[359:352], trn_data[367:360], trn_data[375:368], trn_data[383:376],
                                        trn_data[391:384], trn_data[399:392], trn_data[407:400], trn_data[415:408]
                                      };                        
                        end
                        trn_tx_state <= TRN_TX_STATE_DATA5;                                              
                    end
                end                  
                
                TRN_TX_STATE_DATA5 : begin
                    if (~trn_tdst_rdy_n) begin
                        if (trn_addr_64) begin
                            trn_td <= { trn_data[391:384], trn_data[399:392], trn_data[407:400], trn_data[415:408],
                                        trn_data[423:416], trn_data[431:424], trn_data[439:432], trn_data[447:440]
                                      };
                        end
                        else begin
                            trn_td <= { trn_data[423:416], trn_data[431:424], trn_data[439:432], trn_data[447:440],
                                        trn_data[455:448], trn_data[463:456], trn_data[471:464], trn_data[479:472]
                                      };                        
                        end                  
                        trn_tx_state <= TRN_TX_STATE_DATA6;                                              
                    end
                end                            
                
                TRN_TX_STATE_DATA6 : begin
                    if (~trn_tdst_rdy_n) begin
                        if (trn_addr_64) begin
                            trn_td <= { trn_data[455:448], trn_data[463:456], trn_data[471:464], trn_data[479:472],
                                        trn_data[487:480], trn_data[495:488], trn_data[503:496], trn_data[511:504]
                                      };
                                  
                            if (trn_len == 6'h1) begin // end of TW
                                trn_teof_n <= 1'b0;
                                trn_trem_n <= 1'b0;
                                                                  
                                trn_tx_state <= TRN_TX_STATE_IDLE;
                            end                        
                            else begin  // continue TW
                                trn_len <= trn_len - 1'b1;
                                trn_tw_wait <= 1'b0;
                                trn_tx_state <= TRN_TX_STATE_WR_CONT;
                            end
                        end
                        
                        else begin      // MW32
                            if (trn_len == 6'h1) begin // end of TW
                                trn_td <= { trn_data[487:480], trn_data[495:488], trn_data[503:496], trn_data[511:504], 32'b0};
                                                                  
                                trn_teof_n <= 1'b0;
                                trn_trem_n <= 1'b1;                                                                                                                 
                                trn_tx_state <= TRN_TX_STATE_IDLE;
                            end                        
                            else begin  // continue TW
                                trn_len <= trn_len - 1'b1;
    
                                if (tw_req) begin
                                    tw_grant <= 1'b1;
                                    tr_grant_last <= 1'b0;
                                    trn_data <= tw_data;
                                    trn_tsrc_rdy_n <= 1'b0; 
                                    trn_td <= { trn_data[487:480], trn_data[495:488], trn_data[503:496], trn_data[511:504],
                                                tw_data[7:0], tw_data[15:8],tw_data[23:16], tw_data[31:24]
                                                };
                                                
                                    // fake RX_WR
                                    io_rx_wr_valid <= 1'b1;
                                    io_rx_wr_hdr <= {`CCI_RSP_WR, tw_tag};
                                                                                
                                    trn_tx_state <= TRN_TX_STATE_ADDR;
                                end
                                else begin // wait for next data
                                    trn_tsrc_rdy_n <= 1'b1;
                                    trn_tw_wait <= 1'b1;
                                    trn_tx_state <= TRN_TX_STATE_WR_CONT;                                
                                end
                            end
                        end
                    end                            
                end 
                
                TRN_TX_STATE_WR_CONT : begin
                    if ((~trn_tdst_rdy_n) | (trn_tw_wait & tw_req)) begin                                        
                        if (tw_req) begin
                            tw_grant <= 1'b1;
                            tr_grant_last <= 1'b0;
                            trn_data <= tw_data;
                            trn_tsrc_rdy_n <= 1'b0;
                            
                            if (trn_addr_64) begin
                                trn_td <= { tw_data[7:0], tw_data[15:8],tw_data[23:16], tw_data[31:24],
                                            tw_data[39:32], tw_data[47:40],tw_data[55:48], tw_data[63:56]
                                          };
                                trn_tx_state <= TRN_TX_STATE_DATA0;                                                                              
                            end
                            else begin
                                trn_td <= { trn_data[487:480], trn_data[495:488], trn_data[503:496], trn_data[511:504],
                                            tw_data[7:0], tw_data[15:8],tw_data[23:16], tw_data[31:24]
                                  };
                                trn_tx_state <= TRN_TX_STATE_ADDR;                                                           
                            end
                            
                            // fake RX_WR
                            io_rx_wr_valid <= 1'b1;
                            io_rx_wr_hdr <= {`CCI_RSP_WR, tw_tag};                            
                        end                        
                        else begin
                            trn_tsrc_rdy_n <= 1'b1;
                        end
                    end
                end        
                                                                    
            endcase
        end
    end

        
    //--------------------------------------------------------------------------
    // TRN_RX
    //--------------------------------------------------------------------------    
    assign trn_rx_bar_hit = ~trn_rbar_hit_n[0];
    
    assign trn_rdst_rdy_n = ~trn_rdst_rdy;
//    assign trn_rsrc_dsc = ~trn_rsrc_dsc_n;   
    assign trn_rsrc_dsc = 1'b0;
    assign trn_rnp_ok_n = 1'b0;                // ready to accept non-posted
    assign trn_rsof = ~trn_rsof_n;
    assign trn_reof = ~trn_reof_n;
    assign trn_rsrc_rdy = ~trn_rsrc_rdy_n;
    assign trn_rerrfwd = ~trn_rerrfwd_n;
    
    assign trn_rd_tag = trn_rd[47:40];
    assign trn_rd_len = trn_rd[41:32];

    
    // io rx process
    always @(posedge clk) begin : proc_io_rx_sel_state
        if ((~reset_n) | (~linkup)) begin
            trn_rdst_rdy <= 1'b0;
            rr_split <= 1'b0;
            io_rx_csr_valid <= 1'b0;
            io_rx_rd_valid <= 1'b0;
            trn_rx_fmttype_err <= 1'b0;
            trn_rx_state <= TRN_RX_STATE_IDLE;            
        end
        
        else begin     
            trn_rdst_rdy <= 1'b1;
            io_rx_csr_valid <= 1'b0;
            io_rx_rd_valid <= 1'b0;
 
            case (trn_rx_state)
                TRN_RX_STATE_IDLE : begin
                    // entered from reset, or idle trn_r interface                                                             
                    if (trn_rdst_rdy & trn_rsrc_rdy & trn_rsof & (~trn_rsrc_dsc)) begin   // & trn_rx_bar_hit) begin 
                        case (trn_rd[62:56])
                            `PCIE_FMTTYPE_CPLD : begin   
                                trn_rx_state <= TRN_RX_STATE_CPLD;
                                
                                // synthesis translate_off
                                assert(((trn_rd_len >= 10'h10) | (trn_rd_len == 10'h0)) & (trn_rd_len[3:0] == 4'h0)) else $fatal("incorrect trn_rd_len = %x", trn_rd_len);
                                // synthesis translate_on
                            end // `PCIE_FMTTYPE_CPL_DATA                            
                            
                            `PCIE_FMTTYPE_MEM_WRITE32 : begin
                                if (trn_rx_bar_hit) begin
                                    trn_rx_state <= TRN_RX_STATE_MW32;                            
                                end
                            end

                            `PCIE_FMTTYPE_MEM_WRITE64 : begin
                                if (trn_rx_bar_hit) begin                            
                                    trn_rx_state <= TRN_RX_STATE_MW64_ADDR;                            
                                end
                            end
                                                        
                            default : begin
                                // ignore unsupported TLP
                            end                            
                        endcase // fmttype
                    end
                end
                        
                TRN_RX_STATE_MW32 : begin
                    if (trn_rsrc_dsc) begin
                        trn_rx_state <= TRN_RX_STATE_IDLE; 
                    end
                    
                    else begin
                        if (trn_rdst_rdy & trn_rsrc_rdy) begin
                            io_rx_csr_valid <= 1'b1;
                            io_rx_csr_addr <= trn_rd[47:34];
                            io_rx_csr_data <= {trn_rd[7:0], trn_rd[15:8], trn_rd[23:16], trn_rd[31:24]};  

                            trn_rx_state <= TRN_RX_STATE_IDLE;     
                        end
                    end
                end  // TRN_RX_STATE_MW32                 

                TRN_RX_STATE_MW64_ADDR : begin
                    if (trn_rsrc_dsc) begin
                        trn_rx_state <= TRN_RX_STATE_IDLE; 
                    end
                    
                    else begin                
                        if (trn_rdst_rdy & trn_rsrc_rdy) begin
                            io_rx_csr_addr <= trn_rd[15:2];

                            trn_rx_state <= TRN_RX_STATE_MW64_DATA;  

                            // synthesis translate_off
                            assert(~trn_rsof) else $fatal("unexpecting RSOF here!");
                            assert(~trn_reof) else $fatal("unexpecting REOF here!");
                            // synthesis translate_on                                        

                        end
                    end
                end  // TRN_RX_STATE_MW64_ADDR                                                                            

                TRN_RX_STATE_MW64_DATA : begin   
                    if (trn_rsrc_dsc) begin
                        trn_rx_state <= TRN_RX_STATE_IDLE; 
                    end
                    
                    else begin                                
                        if (trn_rdst_rdy & trn_rsrc_rdy) begin  
                            io_rx_csr_valid <= 1'b1;
                            io_rx_csr_data <= {trn_rd[39:32], trn_rd[47:40], trn_rd[55:48], trn_rd[63:56]};                                                           

                            trn_rx_state <= TRN_RX_STATE_IDLE;
                        end
                    end
                end  // TRN_RX_STATE_MW64_DATA                                  
                                                                                        
                TRN_RX_STATE_CPLD : begin
                    if (trn_rsrc_dsc) begin
                        trn_rx_state <= TRN_RX_STATE_IDLE; 
                    end
                    
                    else begin                   
                        if (trn_rdst_rdy & trn_rsrc_rdy) begin
                            io_rx_rd_tag <= {6'b0, trn_rd_tag};

                            // byte 0 ~ 3
                            rr_1st_dw[7:0] <= trn_rd[31:24];
                            rr_1st_dw[15:8] <= trn_rd[23:16];
                            rr_1st_dw[23:16] <= trn_rd[15:8];
                            rr_1st_dw[31:24] <= trn_rd[7:0];

                            trn_rx_state <= TRN_RX_STATE_CPLD_DATA0;

                            // synthesis translate_off
                            assert(~trn_rsof) else $fatal("unexpecting RSOF here!");
                            assert(~trn_reof) else $fatal("unexpecting REOF here!");
                            // synthesis translate_on                                                          
                        end
                    end
                end  // TRN_RX_STATE_CPLD     
                                
                TRN_RX_STATE_CPLD_DATA0 : begin
                    if (trn_rsrc_dsc) begin
                        trn_rx_state <= TRN_RX_STATE_IDLE; 
                    end
                    
                    else begin                   
                        if (trn_rdst_rdy & trn_rsrc_rdy) begin
                            // byte 0 ~ 3                                                        
                            io_rx_data[31:0] <= rr_1st_dw;
                        
                            // byte 4 ~ 11
                            io_rx_data[39:32] <= trn_rd[63:56];
                            io_rx_data[47:40] <= trn_rd[55:48];
                            io_rx_data[55:48] <= trn_rd[47:40];
                            io_rx_data[63:56] <= trn_rd[39:32];
                            io_rx_data[71:64] <= trn_rd[31:24];
                            io_rx_data[79:72] <= trn_rd[23:16];
                            io_rx_data[87:80] <= trn_rd[15:8];
                            io_rx_data[95:88] <= trn_rd[7:0];

                            trn_rx_state <= TRN_RX_STATE_CPLD_DATA1;

                            // synthesis translate_off
                            assert(~trn_rsof) else $fatal("unexpecting RSOF here!");
                            assert(~trn_reof) else $fatal("unexpecting REOF here!");
                            // synthesis translate_on                               
                        end
                    end
                end  // TRN_RX_STATE_CPLD_DATA0
                                
                TRN_RX_STATE_CPLD_DATA1 : begin
                    if (trn_rsrc_dsc) begin
                        trn_rx_state <= TRN_RX_STATE_IDLE; 
                    end
                    
                    else begin                   
                        if (trn_rdst_rdy & trn_rsrc_rdy) begin
                            // byte 12 ~ 19
                            io_rx_data[103:96] <= trn_rd[63:56];
                            io_rx_data[111:104] <= trn_rd[55:48];
                            io_rx_data[119:112] <= trn_rd[47:40];
                            io_rx_data[127:120] <= trn_rd[39:32];
                            io_rx_data[135:128] <= trn_rd[31:24];
                            io_rx_data[143:136] <= trn_rd[23:16];
                            io_rx_data[151:144] <= trn_rd[15:8];
                            io_rx_data[159:152] <= trn_rd[7:0];

                            trn_rx_state <= TRN_RX_STATE_CPLD_DATA2;

                            // synthesis translate_off
                            assert(~trn_rsof) else $fatal("unexpecting RSOF here!");
                            assert(~trn_reof) else $fatal("unexpecting REOF here!");
                            // synthesis translate_on                                  
                        end
                    end
                end  // TRN_RX_STATE_CPLD_DATA1

                TRN_RX_STATE_CPLD_DATA2 : begin
                    if (trn_rsrc_dsc) begin
                        trn_rx_state <= TRN_RX_STATE_IDLE; 
                    end
                    
                    else begin   
                        if (trn_rdst_rdy & trn_rsrc_rdy) begin
                            // byte 20 ~ 27
                            io_rx_data[167:160] <= trn_rd[63:56];
                            io_rx_data[175:168] <= trn_rd[55:48];
                            io_rx_data[183:176] <= trn_rd[47:40];
                            io_rx_data[191:184] <= trn_rd[39:32];
                            io_rx_data[199:192] <= trn_rd[31:24];
                            io_rx_data[207:200] <= trn_rd[23:16];
                            io_rx_data[215:208] <= trn_rd[15:8];
                            io_rx_data[223:216] <= trn_rd[7:0];

                            trn_rx_state <= TRN_RX_STATE_CPLD_DATA3;

                            // synthesis translate_off
                            assert(~trn_rsof) else $fatal("unexpecting RSOF here!");
                            assert(~trn_reof) else $fatal("unexpecting REOF here!");
                            // synthesis translate_on                          
                        end
                    end
                end  // TRN_RX_STATE_CPLD_DATA2

                TRN_RX_STATE_CPLD_DATA3 : begin
                    if (trn_rsrc_dsc) begin
                        trn_rx_state <= TRN_RX_STATE_IDLE; 
                    end
                    
                    else begin                   
                        if (trn_rdst_rdy & trn_rsrc_rdy) begin
                            // byte 28 ~ 35
                            io_rx_data[231:224] <= trn_rd[63:56];
                            io_rx_data[239:232] <= trn_rd[55:48];
                            io_rx_data[247:240] <= trn_rd[47:40];
                            io_rx_data[255:248] <= trn_rd[39:32];
                            io_rx_data[263:256] <= trn_rd[31:24];
                            io_rx_data[271:264] <= trn_rd[23:16];
                            io_rx_data[279:272] <= trn_rd[15:8];
                            io_rx_data[287:280] <= trn_rd[7:0];

                            trn_rx_state <= TRN_RX_STATE_CPLD_DATA4;

                            // synthesis translate_off
                            assert(~trn_rsof) else $fatal("unexpecting RSOF here!");
                            assert(~trn_reof) else $fatal("unexpecting REOF here!");
                            // synthesis translate_on                                                           
                        end
                    end
                end  // TRN_RX_STATE_CPLD_DATA3
                                      
                TRN_RX_STATE_CPLD_DATA4 : begin
                    if (trn_rsrc_dsc) begin
                        trn_rx_state <= TRN_RX_STATE_IDLE; 
                    end
                    
                    else begin                   
                        if (trn_rdst_rdy & trn_rsrc_rdy) begin
                            // byte 36 ~ 43
                            io_rx_data[295:288] <= trn_rd[63:56];
                            io_rx_data[303:296] <= trn_rd[55:48];
                            io_rx_data[311:304] <= trn_rd[47:40];
                            io_rx_data[319:312] <= trn_rd[39:32];
                            io_rx_data[327:320] <= trn_rd[31:24];
                            io_rx_data[335:328] <= trn_rd[23:16];
                            io_rx_data[343:336] <= trn_rd[15:8];
                            io_rx_data[351:344] <= trn_rd[7:0];

                            trn_rx_state <= TRN_RX_STATE_CPLD_DATA5;

                            // synthesis translate_off
                            assert(~trn_rsof) else $fatal("unexpecting RSOF here!");
                            assert(~trn_reof) else $fatal("unexpecting REOF here!");
                            // synthesis translate_on                             
                        end
                    end
                end  // TRN_RX_STATE_CPLD_DATA4
                                          
                TRN_RX_STATE_CPLD_DATA5 : begin
                    if (trn_rsrc_dsc) begin
                        trn_rx_state <= TRN_RX_STATE_IDLE; 
                    end
                    
                    else begin                   
                        if (trn_rdst_rdy & trn_rsrc_rdy) begin
                            // byte 44 ~ 51
                            io_rx_data[359:352] <= trn_rd[63:56];
                            io_rx_data[367:360] <= trn_rd[55:48];
                            io_rx_data[375:368] <= trn_rd[47:40];
                            io_rx_data[383:376] <= trn_rd[39:32];
                            io_rx_data[391:384] <= trn_rd[31:24];
                            io_rx_data[399:392] <= trn_rd[23:16];
                            io_rx_data[407:400] <= trn_rd[15:8];
                            io_rx_data[415:408] <= trn_rd[7:0];

                            trn_rx_state <= TRN_RX_STATE_CPLD_DATA6;

                            // synthesis translate_off
                            assert(~trn_rsof) else $fatal("unexpecting RSOF here!");
                            assert(~trn_reof) else $fatal("unexpecting REOF here!");
                            // synthesis translate_on                                  
                        end
                    end
                end  // TRN_RX_STATE_CPLD_DATA5
                                          
                TRN_RX_STATE_CPLD_DATA6 : begin
                    if (trn_rsrc_dsc) begin
                        trn_rx_state <= TRN_RX_STATE_IDLE; 
                    end
                    
                    else begin                   
                        if (trn_rdst_rdy & trn_rsrc_rdy) begin
                            // byte 52 ~ 59
                            io_rx_data[423:416] <= trn_rd[63:56];
                            io_rx_data[431:424] <= trn_rd[55:48];
                            io_rx_data[439:432] <= trn_rd[47:40];
                            io_rx_data[447:440] <= trn_rd[39:32];
                            io_rx_data[455:448] <= trn_rd[31:24];
                            io_rx_data[463:456] <= trn_rd[23:16];
                            io_rx_data[471:464] <= trn_rd[15:8];
                            io_rx_data[479:472] <= trn_rd[7:0];

                            trn_rx_state <= TRN_RX_STATE_CPLD_DATA7;

                            // synthesis translate_off
                            assert(~trn_rsof) else $fatal("unexpecting RSOF here!");
                            assert(~trn_reof) else $fatal("unexpecting REOF here!");
                            // synthesis translate_on                                 
                        end
                    end
                end  // TRN_RX_STATE_CPLD_DATA6
                                          
                TRN_RX_STATE_CPLD_DATA7 : begin
                    if (trn_rsrc_dsc) begin
                        trn_rx_state <= TRN_RX_STATE_IDLE; 
                    end
                    
                    else begin                   
                        if (trn_rdst_rdy & trn_rsrc_rdy) begin
                            // byte 60 ~ 63
                            io_rx_data[487:480] <= trn_rd[63:56];
                            io_rx_data[495:488] <= trn_rd[55:48];
                            io_rx_data[503:496] <= trn_rd[47:40];
                            io_rx_data[511:504] <= trn_rd[39:32];

                            io_rx_rd_valid <= 1'b1;
                            
                            if (trn_reof) begin
                                trn_rx_state <= TRN_RX_STATE_IDLE;
                            end

                            else begin                            
                                rr_1st_dw[7:0] <= trn_rd[31:24];
                                rr_1st_dw[15:8] <= trn_rd[23:16];
                                rr_1st_dw[23:16] <= trn_rd[15:8];
                                rr_1st_dw[31:24] <= trn_rd[7:0];

                                trn_rx_state <= TRN_RX_STATE_CPLD_DATA0;
                            end 

                            // synthesis translate_off
                            assert(~trn_rsof) else $fatal("unexpecting RSOF here!");
                            // synthesis translate_on                                                                                                       
                        end
                    end
                end  // TRN_RX_STATE_CPLD_DATA7

            endcase
        end
    end 
    
                   
    //----------------------------------------------------------------------------------                    
    // debug
    //----------------------------------------------------------------------------------
    always @(posedge clk) begin
        if (~reset_n | csr_reset) begin
            trn_terr_drop <= 1'b0;
            trn_tbuf_err <= 1'b0;
            trn_rx_data_err <= 1'b0;
        end

        else begin 
            if (~trn_terr_drop_n) trn_terr_drop <= 1'b1;            
            if ((~trn_tdst_rdy_n) & (trn_tbuf_av == 6'b0)) trn_tbuf_err <= 1'b1;

            if (trn_rerrfwd) trn_rx_data_err <= 1'b1;
        end
    end
    
endmodule        





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


`include "spl_defines.vh"


module spl_core (
    input  wire                             clk,
    input  wire                             reset_n,

    // AFU reset, enable
    output wire                             spl_enable,
    output wire                             spl_reset,
           
    // AFU TX read request
    output wire                             spl_tx_rd_almostfull,
    input  wire                             afu_tx_rd_valid,
    input  wire [98:0]                      afu_tx_rd_hdr,
    
    // AFU TX write request
    output wire                             spl_tx_wr_almostfull,
    input  wire                             afu_tx_wr_valid,
    input  wire                             afu_tx_intr_valid,
    input  wire [98:0]                      afu_tx_wr_hdr,    
    input  wire [511:0]                     afu_tx_data,
    
    // AFU RX read response
    output reg                              spl_rx_rd_valid,
    output reg                              spl_rx_wr_valid0,
    output reg                              spl_rx_cfg_valid,
    output wire                             spl_rx_intr_valid0,
    output wire                             spl_rx_umsg_valid,
    output reg  [`CCI_RX_HDR_WIDTH-1:0]     spl_rx_hdr0,
    output reg  [511:0]                     spl_rx_data,
    
    // AFU RX write response
    output reg                              spl_rx_wr_valid1,
    output wire                             spl_rx_intr_valid1,
    output reg  [`CCI_RX_HDR_WIDTH-1:0]     spl_rx_hdr1,            
    
    // spl_core --> spl_io, TX_RD request
    input  wire                             io_trq_re,
    output wire [`SPL_TRQ_WIDTH-1:0]        cor_trq_dout,
    output wire                             cor_trq_empty,
    output wire                             cor_trq_valid,

    // spl_core --> spl_io, TX_WR request  
    input  wire                             io_twq_re,
    output wire [`SPL_TWQ_WIDTH-1:0]        cor_twq_dout,
    output wire                             cor_twq_empty,
    output wire                             cor_twq_valid,

    // spl_core<->spl_io RX_RD response
    input  wire                             io_rx_rd_valid,
    input  wire [13:0]                      io_rx_rd_tag,
    input  wire [511:0]                     io_rx_data,    
    
    // spl_csr --> spl_cor, RX CSR SWW
    input  wire                             csr_cfg_valid,
    input  wire [13:0]                      csr_cfg_addr,
    input  wire [31:0]                      csr_cfg_data,
    input  wire                             csr_afu_cfg_valid,
    
    // spl_io-->spl_core, RX WR    
    input  wire                             io_rx_wr_valid0,    
    input  wire [`CCI_RX_HDR_WIDTH-1:0]     io_rx_wr_hdr0,
    input  wire                             io_rx_wr_valid1,    
    input  wire [`CCI_RX_HDR_WIDTH-1:0]     io_rx_wr_hdr1,
            
    // spl_csr-->spl_core CTX_BASE, spl_id, csr_reset, csr_enable 
    input  wire                             csr_enable,
    input  wire                             csr_reset,   
    
    input  wire                             csr_dsr_base_valid,
    input  wire [31:0]                      csr_dsr_base,     
    
    input  wire                             csr_ctx_base_valid,
    input  wire [31:0]                      csr_ctx_base    
);


    localparam SPL_ID               = 32'h11100101;        
        
    localparam [2:0]
        SPL_TX_RD_STATE_IDLE       = 3'b000,
        SPL_TX_RD_STATE_CTX_RD     = 3'b001,
        SPL_TX_RD_STATE_PT_RD      = 3'b010,
        SPL_TX_RD_STATE_PT_VALID   = 3'b011,                 
        SPL_TX_RD_STATE_DONE       = 3'b100;
        
    localparam [1:0]
        COR_RX_RD_STATE_CTX        = 2'b00,
        COR_RX_RD_STATE_PT         = 2'b01,
        COR_RX_RD_STATE_AFU        = 2'b10;
        
                
    reg  [31:0]                     dsr_status_addr;
    wire                            dsr_id_update;
    reg                             dsr_id_update_done;
    wire                            dsr_status_update;
    reg                             dsr_status_update_done;
    
    reg  [2:0]                      spl_tx_rd_state;                   
      
    reg                             ctx_valid;                         
    reg  [31:0]                     ctx_pt_base;                       
    reg  [10:0]                     ctx_pt_length;                     
    reg  [`VIR_ADDR_WIDTH -1:0]     afu_vir_base;                      
    reg                             pt_valid;                          
    reg  [10:0]                     pt_rd_cnt;                         
    reg  [31:0]                     pt_rd_addr;                        
    reg  [9:0]                      pt_wr_addr;                        
    reg  [10:0]                     pt_wr_cnt;                         

    reg                             pt_we;                          
    reg  [9:0]                      pt_waddr;                        
    wire [9:0]                      tr_pt_raddr;
    wire [9:0]                      pt_addr0;
    reg 			    tr_pt_re;
    reg  [16:0]                     pt_din;                         
    wire [16:0]                     tr_pt_dout;                        
    
    wire [9:0]                      tw_pt_raddr;
    reg                             tw_pt_re;
    wire [16:0]                     tw_pt_dout;                        
        
    reg  [1:0]                      cor_rx_rd_state;                   
    
    reg                             afu_tx_rd_start;    
    reg                             afu_tx_rd_valid_d1;
    reg                             afu_tx_rd_valid_d2;
    reg  [`VIR_ADDR_WIDTH -1:0]     afu_tx_rd_vir_addr_d1;
    wire [31:0]                     afu_tx_rd_phy_addr;       
    reg  [`VIR_ADDR_WIDTH -1:0]     afu_tx_rd_rel_addr_d1;                          
    reg  [`VIR_ADDR_WIDTH -1:0]     afu_tx_rd_rel_addr_d2; 
    reg                             afu_tx_rd_rel_addr_carry;
    wire [5:0]                      afu_tx_rd_len;
    reg  [5:0]                      afu_tx_rd_len_d1;
    reg  [5:0]                      afu_tx_rd_len_d2;   
    wire [13:0]                     afu_tx_rd_tag;
    reg  [13:0]                     afu_tx_rd_tag_d1;
    reg  [13:0]                     afu_tx_rd_tag_d2;   
         
    reg                             afu_tx_wr_start;      
    reg  [`VIR_ADDR_WIDTH -1:0]     afu_tx_wr_vir_addr_d1;           
    wire [31:0]                     afu_tx_wr_phy_addr;
    reg  [31:0]                     afu_tx_wr_addr_d1;
    reg  [31:0]                     afu_tx_wr_addr_d2;
    reg  [`VIR_ADDR_WIDTH -1:0]     afu_tx_wr_rel_addr_d1; 
    reg  [`VIR_ADDR_WIDTH -1:0]     afu_tx_wr_rel_addr_d2; 
    reg                             afu_tx_wr_rel_addr_carry;
    reg  [511:0]                    afu_tx_data_d1;
    reg  [511:0]                    afu_tx_data_d2;        
    wire                            afu_tx_wr_mem_valid;
    wire                            afu_tx_wr_dsr_valid;
    wire                            afu_tx_wr_fence_valid;
    reg                             afu_tx_wr_mem_valid_d1;
    reg                             afu_tx_wr_dsr_valid_d1;
    reg                             afu_tx_wr_fence_valid_d1;
    reg                             afu_tx_wr_mem_valid_d2;
    reg                             afu_tx_wr_dsr_valid_d2;
    reg                             afu_tx_wr_fence_valid_d2;
    reg  [1:0]                      afu_tx_wr_cmd;
    reg  [1:0]                      afu_tx_wr_cmd_d1;    
    reg  [1:0]                      afu_tx_wr_cmd_d2;
    wire [5:0]                      afu_tx_wr_len;
    reg  [5:0]                      afu_tx_wr_len_d1;
    reg  [5:0]                      afu_tx_wr_len_d2;    
    reg  [13:0]                     afu_tx_wr_tag_d1;
    reg  [13:0]                     afu_tx_wr_tag_d2;
              
    wire                            afu_tx_wr_thru_valid;
    wire                            afu_tx_wr_line_valid;
                                             
    reg                             cor_tx_rd_valid;
    reg  [`SPL_TAG_WIDTH-1:0]       cor_tx_rd_tag; 
    reg  [31:0]                     cor_tx_rd_addr;
    reg  [5:0]                      cor_tx_rd_len;
                                                 
    reg  [`SPL_TAG_WIDTH-1:0]       tr_tag;    
    reg  [`SPL_TAG_WIDTH:0]         tr_pend_cnt;
    reg                             tr_pend_cnt_inc;
    reg                             tr_pend_cnt_dec;

    reg  [12:0]                     tw_tag;                
    reg  [`SPL_WTAG_WIDTH:0]        tw_pend_cnt;
                    
    reg  [511:0]                    spl_rx_rd_data;
    reg  [31:0]                     spl_rx_cfg_data;
    reg  [11:0]                     spl_rx_cfg_addr;
    reg  [13:0]                     spl_rx_rd_tag;
                
    reg                             cor_tx_wr_valid;
    reg  [1:0]                      cor_tx_wr_cmd;
    reg  [5:0]                      cor_tx_wr_len;
    reg  [31:0]                     cor_tx_wr_addr;
    reg  [13:0]                     cor_tx_wr_tag;
    reg  [511:0]                    cor_tx_data;
    wire                            twq_full    /* synthesis syn_keep=1 */;
    wire [3:0]                      twq_count   /* synthesis syn_keep=1 */;
    wire                            twq_almostfull;
    
    wire                            trq_full    /* synthesis syn_keep=1 */;
    wire [3:0]                      trq_count   /* synthesis syn_keep=1 */;
    wire                            trq_almostfull;

    reg  [`MAX_NUM_TAGS-1:0]        pend_tag_valid;
    reg  [`SPL_TAG_WIDTH-1:0]       pend_q_wi;
    reg  [`SPL_TAG_WIDTH-1:0]       pend_q_ri;
                                                   
    reg  [`MAX_NUM_TAGS-1:0]        rob_valid;    
    reg                             rob_we;
    reg  [`SPL_TAG_WIDTH+`MAX_TRANSFER_SIZE-2:0]    rob_waddr;
    reg  [511:0]                    rob_wdata;
    reg                             rob_re;
    reg                             rob_re_d1; 
    reg  [`SPL_TAG_WIDTH+`MAX_TRANSFER_SIZE-2:0]    rob_raddr;
    wire [511:0]                    rob_rdata;
    
    reg                             rx_rd_valid;
    reg  [13:0]                     rx_rd_tag;
    wire [`SPL_TAG_WIDTH-1:0]       rr_tag;
    reg  [511:0]                    rx_data;
    
    wire [`SPL_TAG_WIDTH-1:0]       curr_pend_tag;
    reg  [`SPL_TAG_WIDTH-1:0]       curr_pend_tag_d1;
    reg  [`SPL_TAG_WIDTH-1:0]       curr_pend_tag_d2;
                                
    reg                             csr_cfg_valid_d1;
    reg                             csr_cfg_valid_d2;
    reg                             csr_cfg_valid_d3;
    reg  [13:0]                     csr_cfg_addr_d1;
    reg  [13:0]                     csr_cfg_addr_d2;
    reg  [13:0]                     csr_cfg_addr_d3;
    reg  [31:0]                     csr_cfg_data_d1;
    reg  [31:0]                     csr_cfg_data_d2;
    reg  [31:0]                     csr_cfg_data_d3;
    

`ifdef VENDOR_XILINX
    (* ram_extract = "yes", ram_style = "distributed" *)  
    reg  [`SPL_TAG_WIDTH-1:0]       pend_tag_q[0:2**`SPL_TAG_WIDTH-1]; 

    (* ram_extract = "yes", ram_style = "distributed" *)  
    reg  [5:0]                      rob_len[0:2**`SPL_TAG_WIDTH-1];        // #CL per entry
        
    (* ram_extract = "yes", ram_style = "distributed" *)         
    reg  [13:0]                     afu_pend_tag[0:2**`SPL_TAG_WIDTH-1];
            
    (* ram_extract = "yes", ram_style = "distributed" *) 
    reg  [5:0]                      pend_len_tab[0:2**`SPL_TAG_WIDTH-1];    
`else
(* ramstyle = "logic" *) reg  [`SPL_TAG_WIDTH-1:0]  pend_tag_q[0:`MAX_NUM_TAGS-1];
(* ramstyle = "logic" *) reg  [13:0]    	    afu_pend_tag[0:`MAX_NUM_TAGS-1];
(* ramstyle = "logic" *) reg  [5:0]     	    rob_len[0:`MAX_NUM_TAGS-1];        // #CL per entry
(* ramstyle = "logic" *) reg  [5:0]                 pend_len_tab[0:`MAX_NUM_TAGS-1];    
`endif
    
    
`ifdef MAX_TRANSFER_SIZE_2
    reg  [`MAX_NUM_TAGS-1:0]        rob_wi;
    reg                             rob_ri;       
`endif
    
    // rx wr buffer
    reg  [`MAX_NUM_WTAGS-1:0]       rw_buf_valid;
    reg  [`CCI_RX_HDR_WIDTH-1:0]    rw_buf_hdr[0:`MAX_NUM_WTAGS-1];
    reg  [`SPL_WTAG_WIDTH-1:0]      rw_buf_rp;
    reg  [`SPL_WTAG_WIDTH-1:0]      rw_buf_wp;

    reg                             spl_rx_cfg_valid_pre;
    reg                             spl_rx_rd_valid_pre;
    reg                             spl_rx_wr_valid0_pre;
    
    reg  [17:0]                     spl_rx_rd_hdr0;    
    reg  [17:0]                     spl_rx_wr_hdr0;    
    reg  [17:0]                     spl_rx_cfg_hdr0;    

    integer                         i;    
    reg                             initial_reset_done = 1'b0;   

                                    
    // synthesis translate_off    
    reg  [`MAX_NUM_TAGS-1:0]        rob_we_cnt;
    reg  [`MAX_NUM_TAGS-1:0]        rob_re_cnt;
    // synthesis translate_on                
    
    wire            afu_rw_valid0;
    wire            afu_rw_valid1;
         
    wire [35:0] cs_control;                                    
    

    // page table
    spl_pt_mem #(.ADDR_WIDTH           (10),
                 .DATA_WIDTH           (17)
    ) pagetable (
        .clk        (clk),             
        
        .we0		(pt_we),
        .addr0      (pt_addr0),
        .din0       (pt_din),
		.re0	  	(tr_pt_re),  		
        .dout0      (tr_pt_dout),
        
		.re1	    (tw_pt_re), 
        .addr1      (tw_pt_raddr),  
        .dout1      (tw_pt_dout)                           
    );
    
    
    // TX_WR transmit queue            
    spl_fifo #(.FIFO_WIDTH(`SPL_TWQ_WIDTH),        // data(512) + len(6) + cmd(2) + addr(32) +tag(14) = 566
               .FIFO_DEPTH_BITS(4),
               .FIFO_ALMOSTFULL_THRESHOLD(8)
              ) txwr_queue(
        .clk                (clk),
        .reset_n            (reset_n & (~csr_reset)),
        .din                ({cor_tx_data, cor_tx_wr_len, cor_tx_wr_cmd, cor_tx_wr_addr, cor_tx_wr_tag}),
        .we                 (cor_tx_wr_valid),
        .re                 (io_twq_re),
        .dout               (cor_twq_dout),
        .empty              (cor_twq_empty),
        .valid              (cor_twq_valid),
        .full               (twq_full),
        .count              (twq_count),
        .almostfull         (twq_almostfull)
    );              
          
                
    // TX_RD transmit queue    
    spl_fifo #(.FIFO_WIDTH(`SPL_TRQ_WIDTH),        // addr(32) + len(6) + tag(5 or 8)
               .FIFO_DEPTH_BITS(4),
               .FIFO_ALMOSTFULL_THRESHOLD(8)
              ) txrd_queue(
        .clk                (clk),
        .reset_n            (reset_n & (~csr_reset)),
        .din                ({cor_tx_rd_addr, cor_tx_rd_len, cor_tx_rd_tag}),
        .we                 (cor_tx_rd_valid),
        .re                 (io_trq_re),
        .dout               (cor_trq_dout),
        .empty              (cor_trq_empty),
        .valid              (cor_trq_valid),
        .full               (trq_full),
        .count              (trq_count),
        .almostfull         (trq_almostfull)
    );                
         

    // RX_RD reorder buffer for rd data         
    spl_sdp_mem #(.DATA_WIDTH   (512), 
                  .ADDR_WIDTH   (`SPL_TAG_WIDTH +`MAX_TRANSFER_SIZE - 1)       // transfer size 1, tag width 5 -> 32 entries
    ) reorder_buf (
        .clk        (clk), 
        .we         (rob_we),
        .re         (rob_re),
        .waddr      (rob_waddr),
        .din        (rob_wdata),
        .raddr      (rob_raddr),
        .dout       (rob_rdata) 
    );
                                      
    
    assign spl_reset = csr_reset;
    
       
    //-----------------------------------------------------
    // spl TX_WR request
    //-----------------------------------------------------            
    assign afu_tx_wr_thru_valid = afu_tx_wr_valid & (afu_tx_wr_hdr[55:52] == `CCI_REQ_WR_THRU) & afu_tx_wr_hdr[66];
    assign afu_tx_wr_line_valid = afu_tx_wr_valid & (afu_tx_wr_hdr[55:52] == `CCI_REQ_WR_LINE) & afu_tx_wr_hdr[66];
    assign afu_tx_wr_dsr_valid = afu_tx_wr_valid & 
                                 ((afu_tx_wr_hdr[55:52] == `CCI_REQ_WR_LINE) || (afu_tx_wr_hdr[55:52] == `CCI_REQ_WR_THRU)) &
                                 (~afu_tx_wr_hdr[66]); 
    assign afu_tx_wr_fence_valid = afu_tx_wr_valid & (afu_tx_wr_hdr[55:52] == `CCI_REQ_WR_FENCE); 
    assign afu_tx_wr_mem_valid = afu_tx_wr_thru_valid | afu_tx_wr_line_valid;            
    assign afu_tx_wr_len = afu_tx_wr_hdr[98:93];
        
    assign tw_pt_raddr = afu_tx_wr_rel_addr_d1[24:15];
    assign afu_tx_wr_phy_addr[31:15] = tw_pt_dout;
    assign afu_tx_wr_phy_addr[14:0] = afu_tx_wr_rel_addr_d2[14:0];
    
    assign dsr_id_update = csr_dsr_base_valid & (~dsr_id_update_done);     
    assign dsr_status_update = dsr_id_update_done & pt_valid & (~dsr_status_update_done); 
        
    assign spl_tx_wr_almostfull = twq_almostfull | (tw_pend_cnt >= `MAX_NUM_WTAGS - 6'ha);
    
        
    always @(*) begin
        case ({afu_tx_wr_thru_valid, afu_tx_wr_line_valid, afu_tx_wr_dsr_valid, afu_tx_wr_fence_valid})
            4'b1000: afu_tx_wr_cmd = `COR_REQ_WR_THRU;
            4'b0100: afu_tx_wr_cmd = `COR_REQ_WR_LINE;
            4'b0010: afu_tx_wr_cmd = `COR_REQ_WR_DSR;
            4'b0001: afu_tx_wr_cmd = `COR_REQ_WR_FENCE;
            default: afu_tx_wr_cmd = 2'b0;        
        endcase   
    end
    
    
    always @(posedge clk) begin
        if ((~reset_n) | csr_reset | (~initial_reset_done)) begin
            cor_tx_wr_valid <= 1'b0; 
            dsr_id_update_done <= 1'b0;
            dsr_status_update_done <= 1'b0;
            afu_tx_wr_start <= 1'b0;
            tw_tag <= 13'b0;
            initial_reset_done <= 1'b1;
	    tw_pt_re <= 1'b0;
        end

        else begin
            cor_tx_wr_valid <= 1'b0;
	    tw_pt_re <= 1'b0; 
                                                                                           
            // AUF using TX path
            if (afu_tx_wr_start) begin    
                afu_tx_wr_mem_valid_d1 <= afu_tx_wr_mem_valid;
                afu_tx_wr_mem_valid_d2 <= afu_tx_wr_mem_valid_d1;

                afu_tx_wr_dsr_valid_d1 <= afu_tx_wr_dsr_valid;
                afu_tx_wr_dsr_valid_d2 <= afu_tx_wr_dsr_valid_d1;

                afu_tx_wr_fence_valid_d1 <= afu_tx_wr_fence_valid;
                afu_tx_wr_fence_valid_d2 <= afu_tx_wr_fence_valid_d1;            

                afu_tx_wr_cmd_d1 <= afu_tx_wr_cmd;
                afu_tx_wr_cmd_d2 <= afu_tx_wr_cmd_d1;

                afu_tx_wr_tag_d1 <= afu_tx_wr_hdr[13:0];  
                afu_tx_wr_tag_d2 <= afu_tx_wr_tag_d1;

                afu_tx_wr_addr_d2 <= afu_tx_wr_addr_d1;

                afu_tx_data_d1 <= afu_tx_data; 
                afu_tx_data_d2 <= afu_tx_data_d1;             
            
                cor_tx_data <= afu_tx_data_d2;  
                cor_tx_wr_addr <= afu_tx_wr_addr_d2;
                cor_tx_wr_tag <= afu_tx_wr_tag_d2;
                
                cor_tx_wr_cmd <= afu_tx_wr_cmd_d2;

                afu_tx_wr_len_d1 <= afu_tx_wr_len;
                afu_tx_wr_len_d2 <= afu_tx_wr_len_d1;
                cor_tx_wr_len <= afu_tx_wr_len_d2;
                
                                                                        
                // stage 0: 
                // afu_tx_wr_mem_valid: calcule low 31-bit of afu_tx_wr_rel_addr
                if (afu_tx_wr_mem_valid) begin
                    {afu_tx_wr_rel_addr_carry, afu_tx_wr_rel_addr_d1[31:0]} <= afu_tx_wr_hdr[45:14] - afu_vir_base[31:0];
                    afu_tx_wr_rel_addr_d1[41:32] <= 10'b0; 
                    afu_tx_wr_vir_addr_d1 <= {afu_tx_wr_hdr[76:67], afu_tx_wr_hdr[45:14]}; 
					tw_pt_re <= 1'b1;                          
                end

                if (afu_tx_wr_dsr_valid) begin
                    afu_tx_wr_addr_d1 <= afu_tx_wr_hdr[45:14];
                end
                                
                // stage 1: calculate hi 11 bit of afu_tx_wr_rel_addr; pagetable lookup
                if (afu_tx_wr_mem_valid_d1) begin
                    afu_tx_wr_rel_addr_d2[41:32] <= afu_tx_wr_vir_addr_d1[41:32] - afu_vir_base[41:32] - afu_tx_wr_rel_addr_carry;
                    afu_tx_wr_rel_addr_d2[31:0] <= afu_tx_wr_rel_addr_d1[31:0];
                end

                // stage 2: afu_tx_wr_addr_d2 valid, drive to tx_wr_fifo
                if (afu_tx_wr_mem_valid_d2) begin
                    cor_tx_wr_valid <= 1'b1;                                                            
                    cor_tx_wr_addr <= afu_tx_wr_phy_addr;
                    
                    // synthesis translate_off 
                    assert(afu_tx_wr_rel_addr_d2[41:25] == 17'b0) else $fatal("AFU workspace exceeding 2GB. afu_tx_wr_rel_addr_d2 = %x", afu_tx_wr_rel_addr_d2);
                    assert(afu_tx_wr_tag_d2[13] == 1'b0) else $fatal("AFU tag[13] not zero. afu_tx_wr_tag_d2 = %x", afu_tx_wr_tag_d2);
                    // synthesis translate_on
                end                
                
                if (afu_tx_wr_dsr_valid_d2) begin
                    cor_tx_wr_valid <= 1'b1;
                    cor_tx_wr_len <= 6'h1; 
                end
                                
                if (afu_tx_wr_fence_valid_d2) begin
                    cor_tx_wr_valid <= 1'b1;
                end
            end
            
            
            // SPL using TX path
            else begin
                casex ({afu_tx_wr_dsr_valid, dsr_id_update, dsr_status_update})
                    3'b1?? : begin // AFU issues DSR WR in IDLE state
                        cor_tx_wr_valid <= 1'b1;
                        cor_tx_data <= afu_tx_data;
                        cor_tx_wr_addr <= afu_tx_wr_hdr[45:14];
                        cor_tx_wr_tag <= afu_tx_wr_hdr[13:0];
                        cor_tx_wr_cmd <= `COR_REQ_WR_DSR;  
                        cor_tx_wr_len <= 6'h1;   
                        
                        // synthesis translate_off 
                        assert(afu_tx_wr_hdr[13] == 1'b0) else $fatal("AFU tag[13] not zero. afu_tx_wr_hdr[13:0] = %x", afu_tx_wr_hdr[13:0]);
                        // synthesis translate_on                                               
                    end

                    3'b01? : begin  // DSR_ID
                        cor_tx_wr_valid <= 1'b1;
                        cor_tx_data <= {480'b0, SPL_ID};
                        cor_tx_wr_addr <= csr_dsr_base;                            
                        cor_tx_wr_tag <= {1'b1, tw_tag};
                        cor_tx_wr_cmd <= `COR_REQ_WR_DSR;                            
                        cor_tx_wr_len <= 6'h1;  
                        tw_tag <= tw_tag + 1'b1;                            

                        dsr_status_addr <= csr_dsr_base + 1'b1;                            
                        dsr_id_update_done <= 1'b1;                        
                    end

                    3'b001 : begin  // DSR_STATUS
                        cor_tx_wr_valid <= 1'b1;
//                        cor_tx_data <= {384'b0, dsr_status};
                        cor_tx_data <= {384'b0, 128'b0};
                        cor_tx_wr_addr <= dsr_status_addr;
                        cor_tx_wr_tag <= {1'b1, tw_tag};
                        cor_tx_wr_cmd <= `COR_REQ_WR_DSR; 
                        cor_tx_wr_len <= 6'h1;                            
                        tw_tag <= tw_tag + 1'b1;              

                        dsr_status_update_done <= 1'b1;
                        afu_tx_wr_start <= 1'b1;
                    end                        
                endcase
            end
        end
    end                             
                       
                               
    //-------------------------------------------------------------------------------------
    // TX_RD request - write TX_RD request into TX_RD transmit Q, write tag into pend_tag_q
    //-------------------------------------------------------------------------------------    
    assign spl_tx_rd_almostfull = trq_almostfull | (tr_pend_cnt >= `MAX_NUM_TAGS - 6'h6);
    assign spl_enable = pt_valid & csr_enable & dsr_status_update_done;
    assign tr_pt_raddr = afu_tx_rd_rel_addr_d1[24:15];    
    assign afu_tx_rd_phy_addr[31:15] = tr_pt_dout;
    assign afu_tx_rd_phy_addr[14:0] = afu_tx_rd_rel_addr_d2[14:0];
    assign afu_tx_rd_len = afu_tx_rd_hdr[98:93];
    assign afu_tx_rd_tag = afu_tx_rd_hdr[13:0];
    
    assign curr_pend_tag = pend_tag_q[pend_q_ri];
    assign rr_tag = io_rx_rd_tag[`SPL_TAG_WIDTH-1:0];  
    
    assign pt_addr0 = (pt_we) ? pt_waddr : tr_pt_raddr;
	
	
    always @(posedge clk) begin
        if ((~reset_n) | csr_reset | (~initial_reset_done)) begin
            rob_we <= 1'b0;                                  
            rob_re <= 1'b0; 
            rx_rd_valid <= 1'b0;     
            cor_tx_rd_valid <= 1'b0; 
            afu_tx_rd_start <= 1'b0;             
            tr_pend_cnt_inc <= 1'b0; 
            tr_pend_cnt_dec <= 1'b0;                                     
            spl_tx_rd_state <= SPL_TX_RD_STATE_IDLE;    
            tr_pt_re <= 1'b0;
			            
            for (i = 0; i < `MAX_NUM_TAGS; i = i+1)
                rob_len[i] <= 6'b0;
                               
            tr_tag <= {`SPL_TAG_WIDTH{1'b0}};
            pend_q_wi <= {`SPL_TAG_WIDTH{1'b0}}; 
            pend_tag_valid <= {`MAX_NUM_TAGS{1'b0}}; 
            rob_valid <= {`MAX_NUM_TAGS{1'b0}};
            pend_q_ri <= {`SPL_TAG_WIDTH{1'b0}};        
                                                                        
`ifdef MAX_TRANSFER_SIZE_2                          
            rob_wi <= 32'b0;
            rob_ri <= 1'b0;               
`endif
                                        
            // synthesis translate_off              
            rob_we_cnt <= {`MAX_NUM_TAGS{1'b0}};
            rob_re_cnt <= {`MAX_NUM_TAGS{1'b0}};
            // synthesis translate_on                                                    
        end

        else begin
            afu_tx_rd_valid_d1 <= afu_tx_rd_valid;
            afu_tx_rd_valid_d2 <= afu_tx_rd_valid_d1;
                    
            afu_tx_rd_tag_d1 <= afu_tx_rd_tag;
            afu_tx_rd_tag_d2 <= afu_tx_rd_tag_d1;

            afu_tx_rd_len_d1 <= afu_tx_rd_len;
            afu_tx_rd_len_d2 <= afu_tx_rd_len_d1;
                                
            cor_tx_rd_valid <= 1'b0;
            tr_pend_cnt_inc <= 1'b0;
            
            rob_we <= 1'b0; 
            rob_re <= 1'b0; 
            tr_pend_cnt_dec <= 1'b0;
                           
            rob_re_d1 <= rob_re;
            curr_pend_tag_d1 <= curr_pend_tag;
            curr_pend_tag_d2 <= curr_pend_tag_d1;
                                    
            rx_rd_valid <= 1'b0;

            tr_pt_re <= 1'b0;
                        
            // generate TX_RD request, write into trq
            case (spl_tx_rd_state)
                SPL_TX_RD_STATE_IDLE : begin
                    if (csr_ctx_base_valid & (~trq_almostfull) & (~pend_tag_valid[tr_tag])) begin
                        cor_tx_rd_valid <= 1'b1;
                        cor_tx_rd_addr <= csr_ctx_base;
                        cor_tx_rd_len <= 6'h1;
                        tr_tag <= tr_tag + 1'b1;
                        tr_pend_cnt_inc <= 1'b1;
                        pend_tag_q[pend_q_wi] <= tr_tag;
                        pend_len_tab[tr_tag] <= 6'h1;
                        pend_tag_valid[tr_tag] <= 1'b1;
                        pend_q_wi <= pend_q_wi + 1'b1;                               
                        spl_tx_rd_state <= SPL_TX_RD_STATE_CTX_RD;
                        cor_tx_rd_tag <= tr_tag;                                             
                    end
                end

                SPL_TX_RD_STATE_CTX_RD : begin
                    if (ctx_valid & (~trq_almostfull) & (~pend_tag_valid[tr_tag])) begin
                        cor_tx_rd_valid <= 1'b1;
                        cor_tx_rd_addr <= ctx_pt_base;
                        cor_tx_rd_len <= 6'h1;
                        tr_tag <= tr_tag + 1'b1;
                        tr_pend_cnt_inc <= 1'b1;
                        pend_tag_q[pend_q_wi] <= tr_tag;
                        pend_len_tab[tr_tag] <= 6'h1;
                        pend_tag_valid[tr_tag] <= 1'b1;
                        pend_q_wi <= pend_q_wi + 1'b1;                            
                        pt_rd_cnt <= ctx_pt_length - 1'h1;
                        pt_rd_addr <= ctx_pt_base + 1'b1;
                        spl_tx_rd_state <= SPL_TX_RD_STATE_PT_RD;
                        cor_tx_rd_tag <= tr_tag;                             
                    end
                end    

                SPL_TX_RD_STATE_PT_RD : begin
                    if (|pt_rd_cnt) begin
                        if ((~trq_almostfull) & (~pend_tag_valid[tr_tag])) begin                        
                            cor_tx_rd_valid <= 1'b1;
                            cor_tx_rd_addr <= pt_rd_addr;
                            cor_tx_rd_len <= 6'h1;
                            tr_tag <= tr_tag + 1'b1;
                            tr_pend_cnt_inc <= 1'b1;
                            pend_tag_q[pend_q_wi] <= tr_tag;
                            pend_len_tab[tr_tag] <= 6'h1;
                            pend_tag_valid[tr_tag] <= 1'b1;
                            pend_q_wi <= pend_q_wi + 1'b1;                                
                            pt_rd_cnt <= pt_rd_cnt - 1'b1;
                            pt_rd_addr <= pt_rd_addr + 1'b1;
                            cor_tx_rd_tag <= tr_tag;                                    
                        end
                    end

                    else begin
                        spl_tx_rd_state <= SPL_TX_RD_STATE_PT_VALID;
                    end                                                
                end    

                SPL_TX_RD_STATE_PT_VALID : begin
                    if (pt_valid) begin
                        spl_tx_rd_state <= SPL_TX_RD_STATE_DONE;
                        afu_tx_rd_start <= 1'b1;   
                    end
                end    

                SPL_TX_RD_STATE_DONE : begin
                    // do nothing
                end 
            endcase    
            
            
            // afu TX_RD request
            if (afu_tx_rd_start) begin
                // stage 0: calcule low 31-bit of afu_tx_wr_rel_addr
                if (afu_tx_rd_valid) begin
                    {afu_tx_rd_rel_addr_carry, afu_tx_rd_rel_addr_d1[31:0]} <= afu_tx_rd_hdr[45:14] - afu_vir_base[31:0];
                    afu_tx_rd_rel_addr_d1[41:32] <= 10'b0; 
                    afu_tx_rd_vir_addr_d1 <= {afu_tx_rd_hdr[76:67], afu_tx_rd_hdr[45:14]};
					tr_pt_re <= 1'b1;           
                end
                     
                // stage 1: calculate hi 11 bit of afu_tx_rd_rel_addr; pagetable lookup
                if (afu_tx_rd_valid_d1) begin
                    afu_tx_rd_rel_addr_d2[41:32] <= afu_tx_rd_vir_addr_d1[41:32] - afu_vir_base[41:32] - afu_tx_rd_rel_addr_carry;
                    afu_tx_rd_rel_addr_d2[31:0] <= afu_tx_rd_rel_addr_d1[31:0];
                end    
                
                // stage 2: afu_tx_rd_addr_d2 valid, drive to tx_wr_fifo
                if (afu_tx_rd_valid_d2) begin
                    cor_tx_rd_valid <= 1'b1;
                    cor_tx_rd_addr <= afu_tx_rd_phy_addr;
                    cor_tx_rd_len <= afu_tx_rd_len_d2;
//                    cor_tx_rd_tag <= afu_tx_rd_tag_d2;
                    afu_pend_tag[tr_tag] <= afu_tx_rd_tag_d2;
                    tr_pend_cnt_inc <= 1'b1;
                    tr_tag <= tr_tag + 1'b1;
                    pend_tag_q[pend_q_wi] <= tr_tag;    //afu_tx_rd_tag_d2;
                    pend_len_tab[tr_tag] <= afu_tx_rd_len_d2;
                    pend_tag_valid[tr_tag] <= 1'b1;
                    pend_q_wi <= pend_q_wi + 1'b1;                 
                    cor_tx_rd_tag <= tr_tag;
                                                                            
                    // synthesis translate_off 
                    assert(afu_tx_rd_rel_addr_d2[41:25] == 17'b0) else $fatal("AFU workspace exceeding 2GB. afu_tx_rd_rel_addr_d2 = %x", afu_tx_rd_rel_addr_d2);
                    assert(pend_tag_valid[tr_tag] == 1'b0) else $fatal("tag = %x is pending for completion", tr_tag);
                    assert(afu_tx_rd_tag_d2[13] == 1'b0) else $fatal("tag = %x is invalid", afu_tx_rd_tag_d2);
                    // synthesis translate_on
                end                                               
            end


            // write rob
            if (io_rx_rd_valid) begin
                // reorder buffer bypass
                if ((curr_pend_tag == rr_tag) & pend_tag_valid[rr_tag] &
                    (~csr_afu_cfg_valid) & (~csr_cfg_valid) & (~csr_cfg_valid_d1) & (~csr_cfg_valid_d2) & 
                    (~rob_re) & (~rob_re_d1)) begin
                    rx_rd_valid <= 1'b1;
                    rx_rd_tag <= afu_pend_tag[curr_pend_tag];
                    rx_data <= io_rx_data;  
                    pend_tag_valid[curr_pend_tag] <= 1'b0;
                    pend_q_ri <= pend_q_ri + 1'b1;
                    tr_pend_cnt_dec <= 1'b1;
                    
                    // synthesis translate_off                     
                    assert(pend_tag_valid[curr_pend_tag] == 1'b1) else $fatal("tag = %x is not valid for completion", curr_pend_tag);
                    // synthesis translate_on                                                     
                end
                
                else begin            
                    rob_we <= 1'b1;
                    rob_wdata <= io_rx_data;  
                    rob_len[rr_tag] <= rob_len[rr_tag] + 1'b1;

`ifdef MAX_TRANSFER_SIZE_2     
                    rob_waddr <= {rr_tag, rob_wi[rr_tag]};                        

                    if (pend_len_tab[rr_tag] == 6'h1) begin
                        rob_valid[rr_tag] <= 1'b1;  
                        rob_wi[rr_tag] <= 1'b0;
                    end
                    else begin
                        rob_wi[rr_tag] <= ~rob_wi[rr_tag];                        
                        pend_len_tab[rr_tag] <= pend_len_tab[rr_tag] - 1'b1;
                    end
`else   // MAX_TRANSFER_SIZE_1
                    rob_waddr <= rr_tag;                        
                    rob_valid[rr_tag] <= 1'b1;  
`endif                                                    

                    // synthesis translate_off
                    rob_we_cnt <= rob_we_cnt + 1'b1;
                    // synthesis translate_on                                              
                end
            end
                
            
            // read rob start
            if ((rob_valid[curr_pend_tag]) & (~csr_cfg_valid)) begin  
                rob_re <= 1'b1;  
                
`ifdef MAX_TRANSFER_SIZE_2  
                rob_raddr <= {curr_pend_tag, rob_ri};  

                if (rob_len[curr_pend_tag] == 6'h1) begin              
                    rob_valid[curr_pend_tag] <= 1'b0;
                    rob_len[curr_pend_tag] <= 6'b0;
                    rob_ri <= 1'b0;
                    pend_tag_valid[curr_pend_tag] <= 1'b0;
                    tr_pend_cnt_dec <= 1'b1;
                    pend_q_ri <= pend_q_ri + 1'b1;

                    // synthesis translate_off                     
                    assert(pend_tag_valid[curr_pend_tag] == 1'b1) else $fatal("tag = %x is not valid for completion", curr_pend_tag);
                    // synthesis translate_on                                 
                end
                else begin
                    rob_ri <= ~rob_ri;
                    rob_len[curr_pend_tag] <= rob_len[curr_pend_tag] - 1'b1;
                end                        
`else // MAX_TRANSFER_SIZE_1
                rob_raddr <= curr_pend_tag;  
                rob_valid[curr_pend_tag] <= 1'b0;
                rob_len[curr_pend_tag] <= 6'b0;
                pend_tag_valid[curr_pend_tag] <= 1'b0;
                tr_pend_cnt_dec <= 1'b1;
                pend_q_ri <= pend_q_ri + 1'b1;

                // synthesis translate_off                     
                assert(pend_tag_valid[curr_pend_tag] == 1'b1) else $fatal("tag = %x is not valid for completion", curr_pend_tag);
                // synthesis translate_on                        
`endif                                
                                
                // synthesis translate_off                 
                rob_re_cnt <= rob_re_cnt + 1'b1;
                // synthesis translate_on                                                                       
            end

            // read rob end, data valid, drive rx_rd, inalid rob_valid, update curr_pend_tag
            if (rob_re_d1) begin
                rx_rd_valid <= 1'b1;
                rx_rd_tag <= afu_pend_tag[curr_pend_tag_d2];
                rx_data <= rob_rdata;  
            end             
        end
    end                     

                        
    //-------------------------------------------------
    // tracking pending RD
    //-------------------------------------------------  
    always @(posedge clk) begin
        if ((~reset_n) | csr_reset | (~initial_reset_done)) begin
            tr_pend_cnt <= 0; 
        end

        else begin
            case ({tr_pend_cnt_inc, tr_pend_cnt_dec})            
                2'b01 : begin
                    tr_pend_cnt <= tr_pend_cnt - 1'b1;
                    
                    // synthesis translate_off
                    assert(tr_pend_cnt != 0) else $fatal("received new RX_RD while no pending TX_RD");
                    // synthesis translate_on                    
                end
                
                2'b10 : begin
                    tr_pend_cnt <= tr_pend_cnt + 1'b1;
                    
                    // synthesis translate_off
                    assert(tr_pend_cnt < `MAX_NUM_TAGS) else $fatal("trying to generate new TX_RD while the limit is hit");
                    // synthesis translate_on                                        
                end
                
                default : begin
                    // no change
                end
            endcase
        end
    end
    
                        
    //-------------------------------------------------
    // SPL/AFU RX_RD control
    //-------------------------------------------------  
    assign spl_rx_intr_valid1 = 1'b0;
    assign spl_rx_intr_valid0 = 1'b0;
    assign spl_rx_umsg_valid = 1'b0;
        
        
    always @(posedge clk) begin
        if ((~reset_n) | csr_reset | (~initial_reset_done)) begin
            ctx_valid <= 1'b0;
            pt_we <= 1'b0;
            pt_valid <= 1'b0;
            spl_rx_rd_valid_pre <= 1'b0;
            cor_rx_rd_state <= COR_RX_RD_STATE_CTX;
        end

        else begin
            pt_we <= 1'b0;
            
            case (cor_rx_rd_state)             
                COR_RX_RD_STATE_CTX : begin
                    if (rx_rd_valid) begin
                        ctx_pt_base <= rx_data[37:6];
                        afu_vir_base <= rx_data[111:70];;
                        ctx_pt_length <= rx_data[170:160];    
                        ctx_valid <= 1'b1;
                        pt_wr_cnt <= rx_data[170:160] - 1'b1; 
                        pt_wr_addr <= 10'b0;
                        cor_rx_rd_state <= COR_RX_RD_STATE_PT;

                        // synthesis translate_off
                        assert(rx_data[127:112] == 16'b0) else $fatal("Virtual address exceeding 42 bits %x", io_rx_data[127:70]);
                        // synthesis translate_on
                    end
                end

                COR_RX_RD_STATE_PT : begin
                    if (rx_rd_valid) begin
                        pt_we <= 1'b1;
                        pt_waddr <= pt_wr_addr;
                        pt_din <= rx_data[37:21];           
                                                
                        if (pt_wr_cnt) begin             
                            pt_wr_addr <= pt_wr_addr + 1'b1;
                            pt_wr_cnt <= pt_wr_cnt - 1'b1;
                        end
                        else begin                            
                            cor_rx_rd_state <= COR_RX_RD_STATE_AFU;
                        end
                    end
                end

                COR_RX_RD_STATE_AFU : begin
                    pt_valid <= 1'b1;
                    spl_rx_rd_valid_pre <= rx_rd_valid;
//                    spl_rx_rd_tag <= rx_rd_tag;
                    
                    spl_rx_rd_hdr0 <= {`CCI_RSP_RD, rx_rd_tag};
                    spl_rx_rd_data <= rx_data;
                end           
            endcase
        end
    end
    
               
    //-----------------------------------------------------------------                            
    // output to afu port0 RX. arbitrate between rob, cfg, and wr rsp
    //-----------------------------------------------------------------
    always @(posedge clk) begin
        if ((~reset_n) | csr_reset | (~initial_reset_done)) begin
            spl_rx_cfg_valid_pre <= 1'b0;
            spl_rx_cfg_valid <= 1'b0;
            spl_rx_rd_valid <= 1'b0;
            spl_rx_wr_valid0 <= 1'b0;
        end

        else begin
            spl_rx_cfg_valid <= 1'b0;
            spl_rx_rd_valid <= 1'b0;
            spl_rx_wr_valid0 <= 1'b0;
                    
            spl_rx_cfg_valid_pre <= 1'b0;
            csr_cfg_valid_d1 <= csr_cfg_valid;
            csr_cfg_valid_d2 <= csr_cfg_valid_d1;
            csr_cfg_valid_d3 <= csr_cfg_valid_d2;
            csr_cfg_addr_d1 <= csr_cfg_addr;
            csr_cfg_addr_d2 <= csr_cfg_addr_d1;
            csr_cfg_addr_d3 <= csr_cfg_addr_d2;
            csr_cfg_data_d1 <= csr_cfg_data;
            csr_cfg_data_d2 <= csr_cfg_data_d1;
            csr_cfg_data_d3 <= csr_cfg_data_d2;
            
            if (csr_cfg_valid_d3) begin
                spl_rx_cfg_valid_pre <= 1'b1;
                spl_rx_cfg_hdr0 <= {`CCI_RSP_WR_CSR, csr_cfg_addr_d3};
                spl_rx_cfg_data <= csr_cfg_data_d3;
            end
            
            case ({spl_rx_cfg_valid_pre, spl_rx_rd_valid_pre, spl_rx_wr_valid0_pre})
                3'b100 : begin
                    spl_rx_cfg_valid <= spl_rx_cfg_valid_pre;
                    spl_rx_hdr0 <= spl_rx_cfg_hdr0;
                    spl_rx_data <= spl_rx_cfg_data;
                end
                
                3'b010 : begin
                    spl_rx_rd_valid <= spl_rx_rd_valid_pre;
                    spl_rx_hdr0 <= spl_rx_rd_hdr0;
                    spl_rx_data <= spl_rx_rd_data;                
                end
                
                3'b001 : begin
                    spl_rx_wr_valid0 <= spl_rx_wr_valid0_pre;
                    spl_rx_hdr0 <= spl_rx_wr_hdr0;
                end
                
                default : begin
                
                end                
            endcase
            
            // synthesis translate_off            
            // TODO: checking should include spl_rx_wr_valid0_pre. it is not a problem for afu2 because it does not depend on write response.
            assert((spl_rx_cfg_valid_pre & spl_rx_rd_valid_pre) == 1'b0) else 
                $fatal("spl_rx_cfg_valid_pre and spl_rx_rd_valid_pre asserted at same time");
            // synthesis translate_on
        end
    end
        
        
    //-------------------------------------------------
    // RX_WR response
    //-------------------------------------------------   
    assign afu_rw_valid0 = io_rx_wr_valid0 & (io_rx_wr_hdr0[13] == 1'b0);
    assign afu_rw_valid1 = io_rx_wr_valid1 & (io_rx_wr_hdr1[13] == 1'b0);
    
    
    always @(posedge clk) begin
        if ((~reset_n) | csr_reset | (~initial_reset_done)) begin
            spl_rx_wr_valid1 <= 1'b0;
            spl_rx_wr_valid0_pre <= 1'b0;
            tw_pend_cnt <= {1'b0, `SPL_WTAG_WIDTH'b0};
            rw_buf_rp <= {`SPL_WTAG_WIDTH{1'b0}};
            rw_buf_wp <= {`SPL_WTAG_WIDTH{1'b0}};
            rw_buf_valid <= {`MAX_NUM_WTAGS{1'b0}};   
        end

        else begin    
            spl_rx_wr_valid1 <= 1'b0;
            spl_rx_wr_valid0_pre <= 1'b0;
            
            // sending spl_rx_wr_valid0,1
            case ({rw_buf_valid[rw_buf_rp], rx_rd_valid, afu_rw_valid0, afu_rw_valid1})
                // only rw1, no conflict
                4'b0001,
                4'b0101,
                4'b1101 : begin
                    spl_rx_wr_valid1 <= 1'b1;
                    spl_rx_hdr1 <= io_rx_wr_hdr1;
                end
                
                // only rw0, no rw1, no conflict
                4'b0010, 
                4'b0110,
                4'b1110 : begin
                    spl_rx_wr_valid1 <= 1'b1;
                    spl_rx_hdr1 <= io_rx_wr_hdr0;               
                end

                // both rw0, rw1, no confict with rx_rd_valid
                4'b0011,
                4'b1011 : begin
                    spl_rx_wr_valid0_pre <= 1'b1;
                    spl_rx_wr_hdr0 <= io_rx_wr_hdr0; 
                    spl_rx_wr_valid1 <= 1'b1;
                    spl_rx_hdr1 <= io_rx_wr_hdr1;                                   
                end   
                
                // both rw0, rw1, confict with rx_rd_valid, buffer rw0
                4'b0111,
                4'b1111 : begin
                    spl_rx_wr_valid1 <= 1'b1;
                    spl_rx_hdr1 <= io_rx_wr_hdr1;  
                    
                    rw_buf_valid[rw_buf_wp] <= 1'b1;
                    rw_buf_hdr[rw_buf_wp] <= io_rx_wr_hdr0;
                    rw_buf_wp <= rw_buf_wp + 1'b1;
                end 
                
                // no rw0, no rw1, but buffer is not empty
                4'b1000,
                4'b1100 : begin
                    spl_rx_wr_valid1 <= 1'b1;
                    spl_rx_hdr1 <= rw_buf_hdr[rw_buf_rp];  
                    rw_buf_rp <= rw_buf_rp + 1'b1;
                    rw_buf_valid[rw_buf_rp] <= 1'b0;
                end 
                
                // no rw0, has rw1, no rx_rd_valid, buffer is not empty
                4'b1001 : begin
                    spl_rx_wr_valid0_pre <= 1'b1;
                    spl_rx_wr_hdr0 <= rw_buf_hdr[rw_buf_rp];  
                    rw_buf_rp <= rw_buf_rp + 1'b1;
                    rw_buf_valid[rw_buf_rp] <= 1'b0;
                    
                    spl_rx_wr_valid1 <= 1'b1;
                    spl_rx_hdr1 <= io_rx_wr_hdr1;                    
                end  
                
                // has rw, no rw1, no rx_rd_valid, buffer is not empty
                4'b1010 : begin
                    spl_rx_wr_valid0_pre <= 1'b1;
                    spl_rx_wr_hdr0 <= rw_buf_hdr[rw_buf_rp];  
                    rw_buf_rp <= rw_buf_rp + 1'b1;
                    rw_buf_valid[rw_buf_rp] <= 1'b0;
                    
                    spl_rx_wr_valid1 <= 1'b1;
                    spl_rx_hdr1 <= io_rx_wr_hdr0;                    
                end
            endcase
            
            // tracking pending TX WR
            case ({cor_tx_wr_valid, afu_rw_valid0, afu_rw_valid1})            
                3'b001,
                3'b010,
                3'b111 : begin
                    tw_pend_cnt <= tw_pend_cnt - 1'b1;
                    
                    // synthesis translate_off                    
                    assert(tw_pend_cnt > 0) else $fatal("received new RX_WR while no pending TX_WR");
                    // synthesis translate_on                    
                end
                
                3'b011 : begin
                    tw_pend_cnt <= tw_pend_cnt - 2'h2;
                    
                    // synthesis translate_off                    
                    assert(tw_pend_cnt >= 2'h2) else $fatal("received new RX_WR while no pending TX_WR");
                    // synthesis translate_on                    
                end
                                
                3'b100 : begin
                    tw_pend_cnt <= tw_pend_cnt + 1'b1;
                    
                    // synthesis translate_off
                    assert(tw_pend_cnt < `MAX_NUM_WTAGS) else $fatal("trying to generate new TX_WR while the limit is hit");
                    // synthesis translate_on                                        
                end
                
                default : begin
                    // no change
                end
            endcase            
        end
    end
         
                              
    // synthesis translate_off
    property spl_rx_valid;      
        @(posedge clk) disable iff ((!reset_n) | (csr_reset) | (!initial_reset_done))
            ((spl_rx_rd_valid & spl_rx_cfg_valid) == 1'b0) && 
            ((spl_rx_rd_valid & spl_rx_wr_valid0) == 1'b0) &&
            ((spl_rx_cfg_valid & spl_rx_wr_valid0) == 1'b0);
    endproperty

    assert property(spl_rx_valid) else
        $fatal("spl_rx_valid asserted!");  
        
    property rw_buf_overflow;      
        @(posedge clk) disable iff ((!reset_n) | (csr_reset) | (!initial_reset_done))
            (rw_buf_wp+1'b1) != rw_buf_rp;
    endproperty

    assert property(rw_buf_overflow) else
        $fatal("rw_buf_overflow asserted!");     
		
	property pagetable_no_read_during_wrtie;
		@(posedge clk) disable iff ((!reset_n) | (csr_reset) | (!initial_reset_done))
			((pt_we & tr_pt_re & (pt_waddr == tr_pt_raddr)) == 1'b0) &&
			((pt_we & tw_pt_re & (pt_waddr == tw_pt_raddr)) == 1'b0);
	endproperty
	
	assert property(pagetable_no_read_during_wrtie) else
        $fatal("pagetable read-during-write at same time to location %x", pt_waddr);  	

	property rob_no_read_during_wrtie;
		@(posedge clk) disable iff ((!reset_n) | (csr_reset) | (!initial_reset_done))
			((rob_we & rob_re & (rob_waddr == rob_raddr)) == 1'b0);
	endproperty
	
	assert property(rob_no_read_during_wrtie) else
        $fatal("reorder_buf read-during-write at same time to location %x", rob_waddr);  
		
    // synthesis translate_on
                                                  
endmodule        

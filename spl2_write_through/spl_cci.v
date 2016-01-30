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


module spl_cci(
    input  wire                             clk,
    input  wire                             reset_n,
    input  wire                             csr_reset,
        
    // CCI TX read request
    input  wire                             cci_tx_rd_almostfull,    
    output wire                             spl_tx_rd_valid,
    output wire [60:0]                      spl_tx_rd_hdr,
    
    // CCI TX write request
    input  wire                             cci_tx_wr_almostfull,
    output wire                             spl_tx_wr_valid,
    output wire                             spl_tx_intr_valid,
    output wire [60:0]                      spl_tx_wr_hdr,    
    output wire [511:0]                     spl_tx_data,
    
    // CCI RX read response
    input  wire                             cci_rx_rd_valid,
    input  wire                             cci_rx_wr_valid0,
    input  wire                             cci_rx_cfg_valid,
    input  wire                             cci_rx_intr_valid0,
    input  wire                             cci_rx_umsg_valid,
    input  wire [`CCI_RX_HDR_WIDTH-1:0]     cci_rx_hdr0,
    input  wire [511:0]                     cci_rx_data,
    
    // CCI RX write response
    input  wire                             cci_rx_wr_valid1,
    input  wire                             cci_rx_intr_valid1,
    input  wire [`CCI_RX_HDR_WIDTH-1:0]     cci_rx_hdr1,        
    
    // spl_io-->spl_csr, RX CSR SWW
    output wire                             io_rx_csr_valid,
    output wire [13:0]                      io_rx_csr_addr,
    output wire [31:0]                      io_rx_csr_data,  
    
    // spl_io-->spl_core, RX RD    
    output wire                             io_rx_rd_valid,
    output wire [13:0]                      io_rx_rd_tag,
    output wire [511:0]                     io_rx_data,
            
    // spl_io-->spl_core, RX WR    
    output wire                             io_rx_wr_valid0,    
    output wire [`CCI_RX_HDR_WIDTH-1:0]     io_rx_wr_hdr0,
    output wire                             io_rx_wr_valid1,    
    output wire [`CCI_RX_HDR_WIDTH-1:0]     io_rx_wr_hdr1,
                    
    // spl_core --> spl_io, TX read request
    output reg                              io_trq_re,
    input  wire [`SPL_TRQ_WIDTH-1:0]        cor_trq_dout,
    input  wire                             cor_trq_empty,
    input  wire                             cor_trq_valid,
    
    // spl_core --> spl_io, TX write request
    output reg                              io_twq_re,
    input  wire [`SPL_TWQ_WIDTH-1:0]        cor_twq_dout,
    input  wire                             cor_twq_empty,
    input  wire                             cor_twq_valid
);
    

    localparam [1:0]
        ROB_RD_STATE__0     = 2'b00,
        ROB_RD_STATE__1     = 2'b01,
        ROB_RD_STATE__2     = 2'b10;      
        
    localparam [1:0]
        TX_RD_STATE_IDLE    = 2'b00,
        TX_RD_STATE_0       = 2'b01,
        TX_RD_STATE_1       = 2'b10;
        
    localparam [1:0]        
        TX_WR_STATE__IDLE   = 2'b00,
        TX_WR_STATE__0      = 2'b01,        
        TX_WR_STATE__1      = 2'b10;
        
                
    wire [5:0]                      cci_rx_tid;

    reg  [31:0]                     csr_tx_wr_addr_1;
    reg  [31:0]                     csr_tx_data_1;
    
    reg  [5:0]                      csr_dsr_wtag;
    reg  [5:0]                      cor_dsr_wtag;
        
    reg  [1:0]                      tx_wr_almostfull_cnt;
    reg                             tx_wr_full;
    reg  [1:0]                      tx_wr_state;
    reg  [1:0]                      tx_wr_active;
            
    reg  [1:0]                      tx_rd_almostfull_cnt;
    reg  [1:0]                      tx_rd_state;
    
    wire [5:0]                      rx_rd_tag;
    wire [5:0]                      tx_rd_tag;
    reg  [5:0]                      tx_wr_tag;    
    wire [5:0]                      curr_pend_tag;
    
    reg  [5:0]                      pend_rd_cnt;
    
    reg  [5:0]                      txrd_tagq_din0;
    reg                             txrd_tagq_we0;
    reg  [5:0]                      txrd_tagq_din1;
    reg                             txrd_tagq_we1;
    wire [5:0]                      txrd_tagq_din;
    wire                            txrd_tagq_we;
            
    reg                             txrd_tagq_re;
    wire [5:0]                      txrd_tagq_dout;
    wire                            txrd_tagq_empty;
    wire                            txrd_tagq_almostempty;
    wire                            txrd_tagq_full;
    wire [5:0]                      txrd_tagq_count;
    wire                            txrd_tagq_almostfull;
    
    reg  [1:0]                      tx_rd_active;
    reg  [5:0]                      tag;
    
    reg  [5:0]                      pend_tagq[0:63];
    reg  [5:0]                      pend_tagq_wr_ind;
    reg  [5:0]                      pend_tagq_rd_ind;
    
    wire [544:0]                    twq_din;
    wire                            twq_we;
    reg                             twq_re;
    wire [544:0]                    twq_dout;
    wire                            twq_empty;
    wire                            twq_almostempty;
    wire                            twq_full;
    wire [3:0]                      twq_count;
    wire                            twq_almostfull;
    wire [511:0]                    cor_twq_dout_data;
    wire [31:0]                     cor_twq_dout_addr;    
         
    wire [31:0]                     trq_din;
    wire                            trq_we;
    reg                             trq_re;
    wire [31:0]                     trq_dout;
    wire                            trq_empty;
    wire                            trq_almostempty;
    wire                            trq_full;
    wire [3:0]                      trq_count;
    wire                            trq_almostfull;
    
    reg                             io_trq_re_d1;

    reg  [3:0]                      cci_tx_wr_cmd;
    wire [1:0]                      cor_twq_dout_cmd;
    wire [13:0]                     cor_twq_dout_tag;
        
    wire [13:0]                     cor_trq_dout_tag;
    wire [31:0]                     cor_trq_dout_addr;

    
    //-------------------------------------------------------------------------------------
    // drive TX_WR port
    //-------------------------------------------------------------------------------------
    // data(512) + len(6) + cmd(2) + addr(32) +tag(14) = 566
    assign cor_twq_dout_data = cor_twq_dout[565:54];
    assign cor_twq_dout_cmd = cor_twq_dout[47:46];
    assign cor_twq_dout_addr = cor_twq_dout[45:14];
    assign cor_twq_dout_tag = cor_twq_dout[13:0];    
        
    
    always @(*) begin
        case (cor_twq_dout_cmd)
            `COR_REQ_WR_DSR : cci_tx_wr_cmd = `CCI_REQ_WR_THRU;
            `COR_REQ_WR_THRU : cci_tx_wr_cmd = `CCI_REQ_WR_THRU;
            `COR_REQ_WR_LINE : cci_tx_wr_cmd = `CCI_REQ_WR_LINE;
            `COR_REQ_WR_FENCE : cci_tx_wr_cmd = `CCI_REQ_WR_FENCE;
            default : cci_tx_wr_cmd = 4'b0;
        endcase
    end
    
    
    always @(posedge clk) begin
        if (~reset_n | csr_reset) begin
            io_twq_re <= 1'b0;
        end

        else begin                                
            if (~cci_tx_wr_almostfull) begin
                io_twq_re <= 1'b1;    
            end
            else begin
                io_twq_re <= 1'b0;
            end
        end
    end

    assign spl_tx_intr_valid = 1'b0;
    assign spl_tx_wr_valid = cor_twq_valid;
    assign spl_tx_wr_hdr = {5'b0, cci_tx_wr_cmd, 6'b0, cor_twq_dout_addr, cor_twq_dout_tag}; 
    assign spl_tx_data = cor_twq_dout_data; 
 
     
    //-------------------------------------------------------------------------------------
    // drive TX_RD port
    //-------------------------------------------------------------------------------------
    // addr(32) + len(6) + `SPL_TAG_WIDTH
    assign cor_trq_dout_addr = cor_trq_dout[`SPL_TAG_WIDTH+37:`SPL_TAG_WIDTH+6];
    assign cor_trq_dout_tag = cor_trq_dout[`SPL_TAG_WIDTH-1:0];

    
    always @(posedge clk) begin
        if ((~reset_n) | csr_reset) begin
            io_trq_re <= 1'b0;
        end
        else begin
            if (~cci_tx_rd_almostfull) begin
                io_trq_re <= 1'b1;    
            end 
            else begin
                io_trq_re <= 1'b0;
            end              
        end
    end

    assign spl_tx_rd_valid = cor_trq_valid;
    assign spl_tx_rd_hdr = {5'b0, `CCI_REQ_RD, 6'b0, cor_trq_dout_addr, cor_trq_dout_tag};
         
         
    //------------------------------------------------------
    // forward RX_CFG to spl_csr
    //------------------------------------------------------
    assign io_rx_csr_valid = cci_rx_cfg_valid;
    assign io_rx_csr_addr = cci_rx_hdr0[13:0];
    assign io_rx_csr_data = cci_rx_data[31:0];
  
    
    //-----------------------------------------------------------------
    // RX_RD, forward to spl_core
    //-----------------------------------------------------------------
    assign io_rx_rd_valid = cci_rx_rd_valid;
    assign io_rx_rd_tag = cci_rx_hdr0[13:0];
    assign io_rx_data = cci_rx_data;  

            
    //------------------------------------------------------------------
    // RX WR
    //------------------------------------------------------------------
    assign io_rx_wr_valid0 = cci_rx_wr_valid0;
    assign io_rx_wr_hdr0 = cci_rx_hdr0;
           
    assign io_rx_wr_valid1 = cci_rx_wr_valid1;     
    assign io_rx_wr_hdr1 = cci_rx_hdr1;
                        
endmodule        


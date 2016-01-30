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


module spl_cci_top (
    input  wire                             clk,
    input  wire                             reset_n,
    input  wire                             linkup,
    output wire                             spl_enable,
    output wire                             spl_reset,
        
    
    //------------------------------------------------------
    // AFU interface
    //------------------------------------------------------
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
    output wire                             spl_rx_rd_valid,
    output wire                             spl_rx_wr_valid0,
    output wire                             spl_rx_cfg_valid,
    output wire                             spl_rx_intr_valid0,
    output wire                             spl_rx_umsg_valid,
    output wire [`CCI_RX_HDR_WIDTH-1:0]     spl_rx_hdr0,
    output wire [511:0]                     spl_rx_data,
    
    // AFU RX write response
    output wire                             spl_rx_wr_valid1,
    output wire                             spl_rx_intr_valid1,
    output wire [`CCI_RX_HDR_WIDTH-1:0]     spl_rx_hdr1,
            
        
    //---------------------------------------------------------
    // CCI interface
    //---------------------------------------------------------    
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
    input  wire [`CCI_RX_HDR_WIDTH-1:0]     cci_rx_hdr1
);


    wire                    io_rx_csr_valid;
    wire [13:0]             io_rx_csr_addr;
    wire [31:0]             io_rx_csr_data;
    wire                    io2csr_tx_wr_ready;
    wire                    csr_tx_wr_valid;
    wire [31:0]             csr_tx_wr_addr;
    wire [31:0]             csr_tx_data;
    wire                    io2csr_tx_rd_ready;
    wire                    csr_tx_rd_valid;
    wire [31:0]             csr_tx_rd_addr;
    wire [13:0]             csr_cfg_addr;
    wire [31:0]             csr_cfg_data;
    wire                    csr_afu_cfg_valid;

    wire                    cor_tx_wr_valid;
    wire                    cor_tx_wr_fence;
    wire [31:0]             cor_tx_wr_addr;
    wire [511:0]            cor_tx_data;
    
    wire                    cor_tx_rd_valid;
    wire [31:0]             cor_tx_rd_addr;

    wire                    io_tx_wr_almostfull;

    wire                    io_tx_rd_ready;
    wire                    io_tx_rd_almostfull;

    wire [511:0]            io_rx_data;
    wire                    io_rx_rd_valid;
    wire [13:0]             io_rx_rd_tag;
    
    wire [31:0]             csr_ctx_base;
    wire [31:0]             csr_dsr_base;
    wire [31:0]             csr_id;
    wire                    csr_reset;
    wire                    csr_enable;
    wire                    csr_cfg_valid;
    wire                    csr_dsr_base_valid; 
    wire                    csr_ctx_base_valid; 
       
    wire                            io_twq_re;
    wire [`SPL_TWQ_WIDTH-1:0]       cor_twq_dout;
    wire                            cor_twq_empty;
    wire                            cor_twq_valid;
        
    wire                            io_trq_re;
    wire [`SPL_TRQ_WIDTH-1:0]       cor_trq_dout;
    wire                            cor_trq_empty;
    wire                            cor_trq_valid;
         
    wire                            io_rx_wr_valid0;
    wire [`CCI_RX_HDR_WIDTH-1:0]    io_rx_wr_hdr0;
    wire                            io_rx_wr_valid1;
    wire [`CCI_RX_HDR_WIDTH-1:0]    io_rx_wr_hdr1;
    
    wire                        spl_err_tag_width;
                
                        
    // synthesis translate_off            
    reg     initial_reset_done;
    // synthesis translate_on
            
            
    spl_cci spl_io(
        .clk                        (clk),
        .reset_n                    (reset_n),
        .csr_reset                  (csr_reset),        
        
        // CCI TX read request
        .cci_tx_rd_almostfull       (cci_tx_rd_almostfull),
        .spl_tx_rd_valid            (spl_tx_rd_valid),
        .spl_tx_rd_hdr              (spl_tx_rd_hdr),

        // CCI TX write request
        .cci_tx_wr_almostfull       (cci_tx_wr_almostfull),        
        .spl_tx_wr_valid            (spl_tx_wr_valid),
        .spl_tx_intr_valid          (spl_tx_intr_valid),
        .spl_tx_wr_hdr              (spl_tx_wr_hdr),
        .spl_tx_data                (spl_tx_data),

        // CCI RX read response
        .cci_rx_rd_valid            (cci_rx_rd_valid),
        .cci_rx_wr_valid0           (cci_rx_wr_valid0),
        .cci_rx_cfg_valid           (cci_rx_cfg_valid),
        .cci_rx_intr_valid0         (cci_rx_intr_valid0),
        .cci_rx_umsg_valid          (cci_rx_umsg_valid),
        .cci_rx_hdr0                (cci_rx_hdr0),
        .cci_rx_data                (cci_rx_data),

        // CCI RX write response
        .cci_rx_wr_valid1           (cci_rx_wr_valid1),
        .cci_rx_intr_valid1         (cci_rx_intr_valid1),
        .cci_rx_hdr1                (cci_rx_hdr1),

        // spl_io --> spl_core, RX_RD response
        .io_rx_rd_valid             (io_rx_rd_valid),
        .io_rx_rd_tag               (io_rx_rd_tag),
        .io_rx_data                 (io_rx_data),
        
        // spl_io --> spl_csr, RX CSR SWW
        .io_rx_csr_valid            (io_rx_csr_valid),
        .io_rx_csr_addr             (io_rx_csr_addr),
        .io_rx_csr_data             (io_rx_csr_data),
                
        // spl_io --> spl_core, RX WR response
        .io_rx_wr_valid0            (io_rx_wr_valid0),    
        .io_rx_wr_hdr0              (io_rx_wr_hdr0),
        .io_rx_wr_valid1            (io_rx_wr_valid1),    
        .io_rx_wr_hdr1              (io_rx_wr_hdr1),
        
                        
        // spl_core --> spl_io, TX_RD request
        .io_trq_re                  (io_trq_re),
        .cor_trq_dout               (cor_trq_dout),
        .cor_trq_empty              (cor_trq_empty),
        .cor_trq_valid              (cor_trq_valid),        
       
        // spl_core --> spl_io, TX_WR request
        .io_twq_re                  (io_twq_re),
        .cor_twq_dout               (cor_twq_dout),
        .cor_twq_empty              (cor_twq_empty),
        .cor_twq_valid              (cor_twq_valid)
    );
    
    
    spl_csr spl_csr(
        .clk                        (clk),
        .reset_n                    (reset_n),
        .csr_enable                 (csr_enable),
        .csr_reset                  (csr_reset),
            
        // spl_io --> spl_csr, RX CSR SWW
        .io_rx_csr_valid            (io_rx_csr_valid),
        .io_rx_csr_addr             (io_rx_csr_addr),
        .io_rx_csr_data             (io_rx_csr_data),    
        
        // spl_csr --> spl_core, RX csr sww
        .csr_cfg_valid              (csr_cfg_valid),
        .csr_cfg_addr               (csr_cfg_addr),
        .csr_cfg_data               (csr_cfg_data),
        .csr_afu_cfg_valid          (csr_afu_cfg_valid),
        
        // spl_csr-->spl_core CTX_BASE 
        .csr_dsr_base               (csr_dsr_base),
        .csr_dsr_base_valid         (csr_dsr_base_valid),
        .csr_ctx_base_valid         (csr_ctx_base_valid),
        .csr_ctx_base               (csr_ctx_base)
    );
    

    spl_core spl_core(
        .clk                        (clk),
        .reset_n                    (reset_n),
        .spl_enable                 (spl_enable),
        .spl_reset                  (spl_reset),

        // AFU TX read request
        .spl_tx_rd_almostfull       (spl_tx_rd_almostfull),
        .afu_tx_rd_valid            (afu_tx_rd_valid),
        .afu_tx_rd_hdr              (afu_tx_rd_hdr),
    
        // AFU TX write request
        .spl_tx_wr_almostfull       (spl_tx_wr_almostfull),
        .afu_tx_wr_valid            (afu_tx_wr_valid),
        .afu_tx_intr_valid          (afu_tx_intr_valid),
        .afu_tx_wr_hdr              (afu_tx_wr_hdr),    
        .afu_tx_data                (afu_tx_data),
    
        // AFU RX read response
        .spl_rx_rd_valid            (spl_rx_rd_valid),
        .spl_rx_wr_valid0           (spl_rx_wr_valid0),
        .spl_rx_cfg_valid           (spl_rx_cfg_valid),
        .spl_rx_intr_valid0         (spl_rx_intr_valid0),
        .spl_rx_umsg_valid          (spl_rx_umsg_valid),
        .spl_rx_hdr0                (spl_rx_hdr0),
        .spl_rx_data                (spl_rx_data),
    
        // AFU RX write response
        .spl_rx_wr_valid1           (spl_rx_wr_valid1),
        .spl_rx_intr_valid1         (spl_rx_intr_valid1),
        .spl_rx_hdr1                (spl_rx_hdr1),
        
        // spl_core --> spl_io, TX read request
        .io_trq_re                  (io_trq_re),
        .cor_trq_dout               (cor_trq_dout),
        .cor_trq_empty              (cor_trq_empty),
        .cor_trq_valid              (cor_trq_valid),
       
        // spl_core --> spl_io, TX write request
        .io_twq_re                          (io_twq_re),
        .cor_twq_dout                       (cor_twq_dout),
        .cor_twq_empty                      (cor_twq_empty),
        .cor_twq_valid                      (cor_twq_valid),
       
        // spl_io --> spl_core, RX read response
        .io_rx_rd_valid             (io_rx_rd_valid),
        .io_rx_rd_tag               (io_rx_rd_tag),        
        .io_rx_data                 (io_rx_data),

        // spl_csr --> spl_core, RX csr sww
        .csr_cfg_valid              (csr_cfg_valid),
        .csr_cfg_addr               (csr_cfg_addr),
        .csr_cfg_data               (csr_cfg_data),        
        .csr_afu_cfg_valid          (csr_afu_cfg_valid),
        
        // spl_io --> spl_core, RX WR response
        .io_rx_wr_valid0            (io_rx_wr_valid0),    
        .io_rx_wr_hdr0              (io_rx_wr_hdr0),
        .io_rx_wr_valid1            (io_rx_wr_valid1),    
        .io_rx_wr_hdr1              (io_rx_wr_hdr1),
            
        // spl_csr-->spl_core CTX_BASE 
        .csr_reset                  (csr_reset),
        .csr_enable                 (csr_enable),        
        .csr_dsr_base               (csr_dsr_base),
        .csr_dsr_base_valid         (csr_dsr_base_valid),
        .csr_ctx_base_valid         (csr_ctx_base_valid),
        .csr_ctx_base               (csr_ctx_base)
    );
    
    
    // synthesis translate_off
    initial begin
        initial_reset_done = 0;
        #1;
        @(posedge reset_n);
        initial_reset_done = 1;
    end
    
    property cci_rx_valid;      
        @(posedge clk) disable iff ((!reset_n) | (!initial_reset_done))
            (cci_rx_rd_valid & cci_rx_cfg_valid) == 1'b0;
    endproperty

    assert property(cci_rx_valid) else
        $fatal("cci_rx_valid asserted!"); 
    // synthesis translate_on
        
endmodule        

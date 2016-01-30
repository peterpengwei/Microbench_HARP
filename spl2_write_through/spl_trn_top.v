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


module spl_trn_top (
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
    output wire [17:0]                      spl_rx_hdr0,
    output wire [511:0]                     spl_rx_data,
    
    // AFU RX write response
    output wire                             spl_rx_wr_valid1,
    output wire                             spl_rx_intr_valid1,
    output wire [17:0]                      spl_rx_hdr1,
            
        
    //------------------------------------------------------
    // TRN interface
    //------------------------------------------------------        
    // TRN TX
    input  wire                             trn_tcfg_req_n,        
    input  wire [5:0]                       trn_tbuf_av,
    input  wire                             trn_terr_drop_n,
    input  wire                             trn_tdst_rdy_n,  
    output wire [63:0]                      trn_td,
    output wire                             trn_trem_n,
    output wire                             trn_tsof_n,
    output wire                             trn_teof_n,
    output wire                             trn_tsrc_rdy_n,
    output wire                             trn_terrfwd_n,
    output wire                             trn_tcfg_gnt_n,
    output wire                             trn_tstr_n, 
    output wire                             trn_tsrc_dsc_n,  
         
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
    input  wire [2:0]                       cfg_maxpayload,
    input  wire                             cfg_bme,
    
    output wire                             spl_err_tag_width,
    output wire                             trn_rx_fmttype_err,
    output wire                             trn_terr_drop,
    output wire                             trn_tbuf_err,
    output wire                             trn_rx_data_err
);


    wire                    io_rx_csr_valid;
    wire [13:0]             io_rx_csr_addr;
    wire [31:0]             io_rx_csr_data;
    wire [13:0]             csr_cfg_addr;
    wire [31:0]             csr_cfg_data;

    wire [511:0]            io_rx_data;
    wire                    io_rx_rd_valid;
    wire [13:0]             io_rx_rd_tag;
    
    wire [31:0]             csr_ctx_base;
    wire [31:0]             csr_dsr_base;
    wire                    csr_reset;
    wire                    csr_enable;
    wire                    csr_cfg_valid;
    wire                    csr_dsr_base_valid; 
    wire                    csr_ctx_base_valid; 
       
//    wire                            io_twq_re;
    wire [`SPL_TWQ_WIDTH-1:0]       cor_twq_dout;
    wire                            cor_twq_empty;
    wire                            cor_twq_almostempty;
    
//    wire                            io_trq_re;
    wire [`SPL_TRQ_WIDTH-1:0]       cor_trq_dout;
    wire                            cor_trq_empty;
    wire                            cor_trq_almostempty;
        
    wire                            io_rx_wr_valid0;
    wire [17:0]                     io_rx_wr_hdr0;
    wire                            io_rx_wr_valid1;
    wire [17:0]                     io_rx_wr_hdr1;
                      
    wire [35:0] cs_control;
    
                        
    // synthesis translate_off            
    reg     initial_reset_done;
    // synthesis translate_on
            
            
    spl_trn spl_io(
        .clk                        (clk),
        .reset_n                    (reset_n),
        .linkup                     (linkup),          
                      
        // TRN TX
        .trn_tcfg_req_n             (trn_tcfg_req_n),        
        .trn_tbuf_av                (trn_tbuf_av),
        .trn_terr_drop_n            (trn_terr_drop_n),
        .trn_tdst_rdy_n             (trn_tdst_rdy_n),  
        .trn_td                     (trn_td),
        .trn_trem_n                 (trn_trem_n),
        .trn_tsof_n                 (trn_tsof_n),
        .trn_teof_n                 (trn_teof_n),
        .trn_tsrc_rdy_n             (trn_tsrc_rdy_n),
        .trn_terrfwd_n              (trn_terrfwd_n),
        .trn_tcfg_gnt_n             (trn_tcfg_gnt_n),
        .trn_tstr_n                 (trn_tstr_n), 
        .trn_tsrc_dsc_n             (trn_tsrc_dsc_n),  
         
        // TRN Rx
        .trn_rd                     (trn_rd),
        .trn_rrem_n                 (trn_rrem_n),
        .trn_rsof_n                 (trn_rsof_n),
        .trn_reof_n                 (trn_reof_n),
        .trn_rsrc_rdy_n             (trn_rsrc_rdy_n),
        .trn_rsrc_dsc_n             (trn_rsrc_dsc_n),
        .trn_rerrfwd_n              (trn_rerrfwd_n),
        .trn_rbar_hit_n             (trn_rbar_hit_n),
        .trn_rdst_rdy_n             (trn_rdst_rdy_n),
        .trn_rnp_ok_n               (trn_rnp_ok_n),
                
        // cfg interface
        .cfg_bus_number             (cfg_bus_number),
        .cfg_device_number          (cfg_device_number),
        .cfg_function_number        (cfg_function_number),
//    input  wire [10:0]                      io_max_payload                 // the max payload of an io packet in DW
                    
        // spl_io --> spl_csr, RX CSR SWW     
        .io_rx_csr_valid            (io_rx_csr_valid),
        .io_rx_csr_addr             (io_rx_csr_addr),
        .io_rx_csr_data             (io_rx_csr_data),    

        // spl_io --> spl_core, RX_RD response
        .io_rx_rd_valid             (io_rx_rd_valid),
        .io_rx_rd_tag               (io_rx_rd_tag),
        .io_rx_data                 (io_rx_data),       
                    
        // spl_io --> spl_core, RX WR response
        .io_rx_wr_valid             (io_rx_wr_valid0),    
        .io_rx_wr_hdr               (io_rx_wr_hdr0),
                        
        // spl_core --> spl_io, TX_RD request
        .io_trq_re                  (io_trq_re),
        .cor_trq_dout               (cor_trq_dout),
        .cor_trq_empty              (cor_trq_empty),
        .cor_trq_almostempty        (cor_trq_almostempty),   
                
        // spl_core --> spl_io, TX_WR request
        .io_twq_re                          (io_twq_re),
        .cor_twq_dout                       (cor_twq_dout),
        .cor_twq_empty                      (cor_twq_empty),
        .cor_twq_almostempty                (cor_twq_almostempty),
        
        // spl_csr --> 
        .csr_reset                  (csr_reset),
        .csr_enable                 (csr_enable),  
        
        .trn_rx_fmttype_err         (trn_rx_fmttype_err),
        .trn_terr_drop              (trn_terr_drop),
        .trn_tbuf_err               (trn_tbuf_err),
        .trn_rx_data_err            (trn_rx_data_err)
    );

    
    spl_csr spl_csr(
        .clk                        (clk),
        .reset_n                    (reset_n),
        
        // spl_cr --> all modules
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
        
        // spl_csr-->spl_core CTX_BASE 
        .csr_dsr_base               (csr_dsr_base),
        .csr_dsr_base_valid         (csr_dsr_base_valid),
        .csr_ctx_base_valid         (csr_ctx_base_valid),
        .csr_ctx_base               (csr_ctx_base)
    );
    

    spl_core spl_core(
        .clk                        (clk),
        .reset_n                    (reset_n),

        // from spl_csr 
        .csr_reset                  (csr_reset),
        .csr_enable                 (csr_enable),   

        // to AFU
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
        .cor_trq_almostempty        (cor_trq_almostempty),   

        // spl_core --> spl_io, TX write request
        .io_twq_re                          (io_twq_re),
        .cor_twq_dout                       (cor_twq_dout),
        .cor_twq_empty                      (cor_twq_empty),
        .cor_twq_almostempty                (cor_twq_almostempty),
                
        // spl_io --> spl_core, RX read response
        .io_rx_rd_valid             (io_rx_rd_valid),
        .io_rx_rd_tag               (io_rx_rd_tag),        
        .io_rx_data                 (io_rx_data),

        // spl_csr --> spl_core, RX csr sww
        .csr_cfg_valid              (csr_cfg_valid),
        .csr_cfg_addr               (csr_cfg_addr),
        .csr_cfg_data               (csr_cfg_data),        
        
        // spl_io --> spl_core, RX WR response
        .io_rx_wr_valid0            (io_rx_wr_valid0),    
        .io_rx_wr_hdr0              (io_rx_wr_hdr0),
        .io_rx_wr_valid1            (1'b0),    
        .io_rx_wr_hdr1              (18'b0),
            
        // spl_csr-->spl_core CTX_BASE      
        .csr_dsr_base               (csr_dsr_base),
        .csr_dsr_base_valid         (csr_dsr_base_valid),
        .csr_ctx_base_valid         (csr_ctx_base_valid),
        .csr_ctx_base               (csr_ctx_base),  
        .spl_err_tag_width          (spl_err_tag_width)
    );
    
    
// //     //------------------------------------------------------------------
// //     // for debugging
// //     
// //     always @(posedge clk) begin
// //         io_twq_re_d1 <= io_twq_re;
// //         io_trq_re_d1 <= io_trq_re;
// //     end
// // 
// //     assign cs_trigger = io_twq_re_d1 | io_trq_re_d1 | io_rx_csr_valid | io_rx_wr_valid | io_rx_rd_valid;
// //     
//     chipscope_icon_1 chipscope_icon (
//         .CONTROL0(cs_control) // INOUT BUS [35:0]
//     );
// //         
// //     chipscope_ila chipscope_ila (
// //     .CONTROL(cs_control), // INOUT BUS [35:0]
// //     .CLK(clk), // IN
// // //     .TRIG0(io_rx_rd_valid), // IN BUS [0:0]
// // //     .TRIG1({io_rx_rd_tag, io_rx_data[241:0]}) // IN BUS [255:0]
// //     .TRIG0(io_twq_re_d1), // IN BUS [0:0]
// //     .TRIG1(cor_twq_dout[255:0]) // IN BUS [255:0]    
// //     );
//         
// 
//     chipscope_ila_afu chipscope_ila_afu (
//         .CLK        (clk), // IN    
//         .CONTROL    (cs_control), // INOUT BUS [35:0]
// 
//         .TRIG0      (io_rx_rd_valid), // IN BUS [0:0]
//         .TRIG1      (io_rx_data[63:0]) // IN BUS [63:0]           
//     );
    
    
    
    // synthesis translate_off
    initial begin
        initial_reset_done = 0;
        #1;
        @(posedge reset_n);
        initial_reset_done = 1;
    end
            
    property spl_rx_valid;      
        @(posedge clk) disable iff ((!reset_n) | (spl_reset) | (!initial_reset_done))
            (spl_rx_rd_valid & spl_rx_cfg_valid) == 1'b0;
    endproperty

    assert property(spl_rx_valid) else
        $fatal("spl_rx_valid asserted!");   
    // synthesis translate_on
        
endmodule        

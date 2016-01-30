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


module cci_ext_afu(
  // Link/Protocol (LP) clocks and reset
  input  /*var*/  logic             vl_clk_LPdomain_32ui,                      // CCI Inteface Clock. 32ui link/protocol clock domain.
  input  /*var*/  logic             vl_clk_LPdomain_16ui,                      // 2x CCI interface clock. Synchronous.16ui link/protocol clock domain.
  input  /*var*/  logic             ffs_vl_LP32ui_lp2sy_SystemReset_n,         // System Reset
  input  /*var*/  logic             ffs_vl_LP32ui_lp2sy_SoftReset_n,           // CCI-S soft reset

  // Native CCI Interface (cache line interface for back end)
  /* Channel 0 can receive READ, WRITE, WRITE CSR, UMsg, Interrupt responses.*/
  input  /*var*/  logic      [23:0] ffs_vl24_LP32ui_lp2sy_C0RxHdr,             // System to LP header
  input  /*var*/  logic     [511:0] ffs_vl512_LP32ui_lp2sy_C0RxData,           // System to LP data 
  input  /*var*/  logic             ffs_vl_LP32ui_lp2sy_C0RxWrValid,           // RxWrHdr valid signal 
  input  /*var*/  logic             ffs_vl_LP32ui_lp2sy_C0RxRdValid,           // RxRdHdr valid signal
  input  /*var*/  logic             ffs_vl_LP32ui_lp2sy_C0RxCgValid,           // RxCgHdr valid signal
  input  /*var*/  logic             ffs_vl_LP32ui_lp2sy_C0RxUgValid,           // Rx Umsg Valid signal
  input  /*var*/  logic             ffs_vl_LP32ui_lp2sy_C0RxIrValid,           // Rx Interrupt valid signal
  /* Channel 1 reserved for WRITE, INTERRUPT RESPONSES */
  input  /*var*/  logic      [23:0] ffs_vl24_LP32ui_lp2sy_C1RxHdr,             // System to LP header (Channel 1)
  input  /*var*/  logic             ffs_vl_LP32ui_lp2sy_C1RxWrValid,           // RxData valid signal (Channel 1)
  input  /*var*/  logic             ffs_vl_LP32ui_lp2sy_C1RxIrValid,           // Rx Interrupt valid signal (Channel 1)

  /*Channel 0 reserved for READ REQUESTS ONLY */        
  output /*var*/  logic      [98:0] ffs_vl99_LP32ui_sy2lp_C0TxHdr,             // System to LP header 
  output /*var*/  logic             ffs_vl_LP32ui_sy2lp_C0TxRdValid,           // TxRdHdr valid signals 
  /*Channel 1 reserved for WRITE, INTERRUPT REQUESTS ONLY */       
  output /*var*/  logic      [98:0] ffs_vl99_LP32ui_sy2lp_C1TxHdr,             // System to LP header
  output /*var*/  logic     [511:0] ffs_vl512_LP32ui_sy2lp_C1TxData,           // System to LP data 
  output /*var*/  logic             ffs_vl_LP32ui_sy2lp_C1TxWrValid,           // TxWrHdr valid signal
  output /*var*/  logic             ffs_vl_LP32ui_sy2lp_C1TxIrValid,           // Tx Interrupt valid signal
  /* Tx push flow control */
  input  /*var*/  logic             ffs_vl_LP32ui_lp2sy_C0TxAlmFull,           // Channel 0 almost full
  input  /*var*/  logic             ffs_vl_LP32ui_lp2sy_C1TxAlmFull,           // Channel 1 almost full

  input  /*var*/  logic             ffs_vl_LP32ui_lp2sy_InitDnForSys           // System layer is aok to run
);

/* SPL2 test AFU goes here
*/
    afu_top afu_top(
        .clk                        (vl_clk_LPdomain_32ui),
        .reset_n                    (ffs_vl_LP32ui_lp2sy_SystemReset_n),
        .spl_enable                 (ffs_vl_LP32ui_lp2sy_InitDnForSys),
        .spl_reset                  (~ffs_vl_LP32ui_lp2sy_SoftReset_n),
        
        // AFU TX read request
        .spl_tx_rd_almostfull       (ffs_vl_LP32ui_lp2sy_C0TxAlmFull),
        .afu_tx_rd_valid            (ffs_vl_LP32ui_sy2lp_C0TxRdValid),
        .afu_tx_rd_hdr              (ffs_vl99_LP32ui_sy2lp_C0TxHdr),
    
        // AFU TX write request
        .spl_tx_wr_almostfull       (ffs_vl_LP32ui_lp2sy_C1TxAlmFull),
        .afu_tx_wr_valid            (ffs_vl_LP32ui_sy2lp_C1TxWrValid),
        .afu_tx_intr_valid          (ffs_vl_LP32ui_sy2lp_C1TxIrValid),
        .afu_tx_wr_hdr              (ffs_vl99_LP32ui_sy2lp_C1TxHdr),    
        .afu_tx_data                (ffs_vl512_LP32ui_sy2lp_C1TxData),
    
        // AFU RX read response
        .spl_rx_rd_valid            (ffs_vl_LP32ui_lp2sy_C0RxRdValid),
        .spl_rx_wr_valid0           (ffs_vl_LP32ui_lp2sy_C0RxWrValid),
        .spl_rx_cfg_valid           (ffs_vl_LP32ui_lp2sy_C0RxCgValid),
        .spl_rx_intr_valid0         (ffs_vl_LP32ui_lp2sy_C0RxIrValid),
        .spl_rx_umsg_valid          (ffs_vl_LP32ui_lp2sy_C0RxUgValid),
        .spl_rx_hdr0                (ffs_vl24_LP32ui_lp2sy_C0RxHdr),
        .spl_rx_data                (ffs_vl512_LP32ui_lp2sy_C0RxData),
    
        // AFU RX write response
        .spl_rx_wr_valid1           (ffs_vl_LP32ui_lp2sy_C1RxWrValid),
        .spl_rx_intr_valid1         (ffs_vl_LP32ui_lp2sy_C1RxIrValid),
        .spl_rx_hdr1                (ffs_vl24_LP32ui_lp2sy_C1RxHdr)
    );
    
endmodule

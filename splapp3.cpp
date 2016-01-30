// Copyright (c) 2014-2015, Intel Corporation
//
// Redistribution  and  use  in source  and  binary  forms,  with  or  without
// modification, are permitted provided that the following conditions are met:
//
// * Redistributions of  source code  must retain the  above copyright notice,
//   this list of conditions and the following disclaimer.
// * Redistributions in binary form must reproduce the above copyright notice,
//   this list of conditions and the following disclaimer in the documentation
//   and/or other materials provided with the distribution.
// * Neither the name  of Intel Corporation  nor the names of its contributors
//   may be used to  endorse or promote  products derived  from this  software
//   without specific prior written permission.
//
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
// AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING,  BUT NOT LIMITED TO,  THE
// IMPLIED WARRANTIES OF  MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
// ARE DISCLAIMED.  IN NO EVENT  SHALL THE COPYRIGHT OWNER  OR CONTRIBUTORS BE
// LIABLE  FOR  ANY  DIRECT,  INDIRECT,  INCIDENTAL,  SPECIAL,  EXEMPLARY,  OR
// CONSEQUENTIAL  DAMAGES  (INCLUDING,  BUT  NOT LIMITED  TO,  PROCUREMENT  OF
// SUBSTITUTE GOODS OR SERVICES;  LOSS OF USE,  DATA, OR PROFITS;  OR BUSINESS
// INTERRUPTION)  HOWEVER CAUSED  AND ON ANY THEORY  OF LIABILITY,  WHETHER IN
// CONTRACT,  STRICT LIABILITY,  OR TORT  (INCLUDING NEGLIGENCE  OR OTHERWISE)
// ARISING IN ANY WAY OUT OF THE USE OF THIS SOFTWARE,  EVEN IF ADVISED OF THE
// POSSIBILITY OF SUCH DAMAGE.
//****************************************************************************
#ifdef HAVE_CONFIG_H
# include <config.h>
#endif // HAVE_CONFIG_H

#include <cstring>                        // memcmp
#include <aalsdk/utils/Utilities.h>       // Brings in CL, MB, GB, etc.
#include <aalsdk/utils/CSyncClient.h>     // CSyncClient object
#include <aalsdk/service/ISPLAFU.h>       // Service Interface
#include <aalsdk/service/ISPLClient.h>    // Service Client Interface
#include <aalsdk/kernel/vafu2defs.h>      // AFU structure definitions (brings in spl2defs.h)
#include <aalsdk/AALLoggerExtern.h>       // Logger, used by INFO and ERR macros
#include <aalsdk/aalclp/aalclp.h>         // Command-line processor
#include <aalsdk/service/SPLAFUService.h> // Service Manifest and #defines

using namespace AAL;

#ifdef INFO
# undef INFO
#endif // INFO
#define INFO(x) AAL_INFO(LM_Any, __AAL_SHORT_FILE__ << ':' << __LINE__ << ':' << __AAL_FUNC__ << "() : " << x << std::endl)
#ifdef ERR
# undef ERR
#endif // ERR
#define ERR(x) AAL_ERR(LM_Any, __AAL_SHORT_FILE__ << ':' << __LINE__ << ':' << __AAL_FUNC__ << "() : " << x << std::endl)

// Change DBG_HOOK to 1 if you want an opportunity to attach the debugger.
// After attaching, set gWaitForDebuggerAttach to 0 via the debugger to unblock the app.
#define DBG_HOOK 0
#if DBG_HOOK
btBool gWaitForDebuggerAttach = true;
#endif // DBG_HOOK

/// @addtogroup splapp3
/// @{

// Ugly hack so that Doxygen produces the correct class diagrams.
#define CMyApp CMysplapp3_App

////////////////////////////////////////////////////////////////////////////////
// CMyApp
#define DEFAULT_TARGET_AFU SPLAFU_NVS_VAL_TARGET_SWSIM

/// @brief splapp3-specific instantiation of ISPLClient that receives the event notifications
///        sent by the ISPLAFU.
class CMyApp : public CSyncClient,        // Inherit interface and implementation of IRunTimeClien and IServiceClient
               public ISPLClient          // SPL Client Interface
{
public:
   CMyApp() :
         m_pISPLAFU(NULL),
         m_pServiceBase(NULL),
         m_OneLargeWorkspaceVirt(NULL),
         m_OneLargeWorkspaceSize(0),
         m_AFUDSMVirt(NULL),
         m_AFUDSMSize(0),
         m_AFUTarget(DEFAULT_TARGET_AFU),
         m_WSRequestLen(0)
   {
      SetSubClassInterface(iidSPLClient, dynamic_cast<ISPLClient *>(this));
      m_bIsOK = true;
   }
   ~CMyApp(){}
   btBool IsOK() const { return m_bIsOK && CSyncClient::IsOK(); }

   ///////////////////////////////////////////////////////////////////////////
   // <Extend CSyncClient>
   // First call to CMyApp. Start everything up and then return status.
   // If returns false, need to shut down the runtime and exit.
   bool start( const NamedValueSet &RunTimeArgs, const NamedValueSet &Manifest)
   {
      if ( !syncStart( RunTimeArgs ) ) { // CSyncClient synchronous runtime start
         ERR("Could not start Runtime.");
         return false;
      }
      m_pServiceBase = syncAllocService( Manifest );  // CSyncClient synchronous get pointer
      if ( !m_pServiceBase ) {                        //    to Service Object
         ERR("Could not allocate Service.");          // Error return possible if it cannot
         return false;                                //    be obtained
      }
      // Get pointer to SPL AFU
      m_pISPLAFU = dynamic_ptr<ISPLAFU>( iidSPLAFU, m_pServiceBase);
      ASSERT( m_pISPLAFU );
      if ( !m_pISPLAFU ) {                         // this would represent an internal logic error
         ERR( "Could not access SPL Service.");
         return false;
      }
      return m_bIsOK;
   }
   // Shutdown the RunTime Client, and therefore the RunTime itself
   void stop()
   {
      syncStop();    // use CSyncClient's synchronouse stop
   }
   // </Extend CSyncClient>
   ///////////////////////////////////////////////////////////////////////////

   ///////////////////////////////////////////////////////////////////////////
   // <ISPLClient>

   /// CMyApp Client implementation of ISPLClient::OnWorkspaceAllocated
   virtual void OnWorkspaceAllocated( TransactionID const &TranID,
                                      btVirtAddr           WkspcVirt,
                                      btPhysAddr           WkspcPhys,
                                      btWSSize             WkspcSize)
   {
      OneLarge(WkspcVirt, WkspcPhys, WkspcSize);
      INFO("Got Workspace");
      Post();
   }
   /// CMyApp Client implementation of ISPLClient::OnWorkspaceAllocateFailed
   virtual void OnWorkspaceAllocateFailed( const IEvent &Event)
   {
      m_bIsOK = false;
      OneLarge( NULL, 0, 0);
      ERR("Workspace Allocate Failed");
      Post();
   }
   /// CMyApp Client implementation of ISPLClient::OnWorkspaceFreed
   virtual void OnWorkspaceFreed( TransactionID const &TranID)
   {
      OneLarge( NULL, 0, 0);
      INFO("Freed Workspace");
      Post();
   }
   /// CMyApp Client implementation of ISPLClient::OnWorkspaceFreeFailed
   virtual void OnWorkspaceFreeFailed( const IEvent &Event)
   {
      m_bIsOK = false;
      OneLarge( NULL, 0, 0);
      ERR("Workspace Free Failed");
      Post();
   }
   /// CMyApp Client implementation of ISPLClient::OnTransactionStarted
   virtual void OnTransactionStarted( TransactionID const &TranID,
                                      btVirtAddr           AFUDSMVirt,
                                      btWSSize             AFUDSMSize)
   {
      INFO("Transaction Started");
      AFUDSM(AFUDSMVirt, AFUDSMSize);
      Post();
   }
   /// CMyApp Client implementation of ISPLClient::OnContextWorkspaceSet
   virtual void OnContextWorkspaceSet( TransactionID const &TranID)
   {
      INFO("Context Set");
      Post();
   }
   /// CMyApp Client implementation of ISPLClient::OnTransactionFailed
   virtual void OnTransactionFailed( const IEvent &Event)
   {
      m_bIsOK = false;
      AFUDSM( NULL, 0);
      ERR("Transaction Failed");
      Post();
   }
   /// CMyApp Client implementation of ISPLClient::OnTransactionComplete
   virtual void OnTransactionComplete( TransactionID const &TranID)
   {
      AFUDSM( NULL, 0);
      INFO("Transaction Complete");
      Post();
   }
   /// CMyApp Client implementation of ISPLClient::OnTransactionStopped
   virtual void OnTransactionStopped( TransactionID const &TranID)
   {
      AFUDSM( NULL, 0);
      INFO("Transaction Stopped");
      Post();
   }
   // </ISPLClient>
   ///////////////////////////////////////////////////////////////////////////

   ///////////////////////////////////////////////////////////////////////////
   // <Synchronous versions of ISPLAFU (which includes ICCIAFU>

   /// CMyApp Client synchronous implementation of ISPLAFU::StartTransactionContext
   btBool syncStartTransactionContext(TransactionID const &TranID,
                                  btVirtAddr           Address=NULL,
                                  btTime               Pollrate=0)
   {
      m_pISPLAFU->StartTransactionContext( TranID, Address, Pollrate);
      Wait();                    // Posted in OnTransactionStarted()
      return m_bIsOK;
   }
   /// CMyApp Client synchronous implementation of ISPLAFU::StopTransactionContext
   btBool syncStopTransactionContext(TransactionID const &TranID)
   {
      m_pISPLAFU->StopTransactionContext( TranID);
      Wait();
      return m_bIsOK;
   }
   /// CMyApp Client synchronous implementation of ISPLAFU::SetContextWorkspace
   btBool syncSetContextWorkspace(TransactionID const &TranID,
                                  btVirtAddr           Address,
                                  btTime               Pollrate=0)
   {
      m_pISPLAFU->SetContextWorkspace( TranID, Address, Pollrate);
      Wait();
      return m_bIsOK;
   }
   /// CMyApp Client synchronous implementation of ISPLAFU::WorkspaceAllocate
   btBool syncWorkspaceAllocate(btWSSize             Length,
                                TransactionID const &rTranID)
   {
      m_pISPLAFU->WorkspaceAllocate( Length, rTranID);
      Wait();
      return m_bIsOK;
   }
   /// CMyApp Client synchronous implementation of ISPLAFU::WorkspaceFree
   btBool syncWorkspaceFree(btVirtAddr           Address,
                            TransactionID const &rTranID)
   {
      m_pISPLAFU->WorkspaceFree( Address, rTranID);
      Wait();
      return m_bIsOK;
   }

   // These are already synchronous, but this object is not derived from
   //    ICCIAFU, so must delegate

   /// CMyApp Client delegation of ICCIAFU::CSRRead
   btBool CSRRead(btCSROffset CSR, btCSRValue *pValue)
   {
      return m_pISPLAFU->CSRRead( CSR, pValue);
   }
   /// CMyApp Client delegation of ICCIAFU::CSRWrite
   btBool CSRWrite(btCSROffset CSR, btCSRValue Value)
   {
      return m_pISPLAFU->CSRWrite( CSR, Value);
   }
   /// CMyApp Client delegation of ICCIAFU::CSRWrite64
   btBool CSRWrite64(btCSROffset CSR, bt64bitCSR Value)
   {
      return m_pISPLAFU->CSRWrite64( CSR, Value);
   }
   // </Synchronous versions of ISPLAFU (which includes ICCIAFU>
   ///////////////////////////////////////////////////////////////////////////

   ///////////////////////////////////////////////////////////////////////////
   // Accessors and Mutators

   btVirtAddr OneLargeVirt() const { return m_OneLargeWorkspaceVirt; } ///< Accessor for the AFU Context workspace.
   btWSSize   OneLargeSize() const { return m_OneLargeWorkspaceSize; } ///< Accessor for the AFU Context workspace.

   btVirtAddr AFUDSMVirt()   const { return m_AFUDSMVirt; } ///< Accessor for the AFU DSM workspace.
   btWSSize   AFUDSMSize()   const { return m_AFUDSMSize; } ///< Accessor for the AFU DSM workspace.

   /// Mutator for setting the NVS value that selects the AFU Delegate.
   void AFUTarget(const std::string &target) { m_AFUTarget = target;  }
   /// Accessor for the NVS value that selects the AFU Delegate.
   std::string AFUTarget() const             { return m_AFUTarget;    }

   /// Mutator for setting the AFU Context workspace size.
   void WSRequestLen(btWSSize len)           { m_WSRequestLen = len;  }
   /// Accessor for the AFU Context workspace size.
   btWSSize WSRequestLen() const             { return m_WSRequestLen; }

protected:
   /// Store information about the Virtual Workspace into CMyApp
   void OneLarge(btVirtAddr v, btPhysAddr p, btWSSize s)
   {
      m_OneLargeWorkspaceVirt = v;
      m_OneLargeWorkspaceSize = s;
   }
   /// Store information about the DSM (Device Status Memory) into CMyApp
   void AFUDSM(btVirtAddr v, btWSSize s)
   {
      m_AFUDSMVirt = v;
      m_AFUDSMSize = s;
   }

   // Member variables
   ISPLAFU             *m_pISPLAFU;       ///< Points to the actual AFU, stored here for convenience
   IBase               *m_pServiceBase;   ///< Pointer to Service containing SPL AFU

   btVirtAddr           m_OneLargeWorkspaceVirt; ///< Points to Virtual workspace
   btWSSize             m_OneLargeWorkspaceSize; ///< Length in bytes of Virtual workspace
   btVirtAddr           m_AFUDSMVirt;            ///< Points to DSM
   btWSSize             m_AFUDSMSize;            ///< Length in bytes of DSM

   std::string          m_AFUTarget;      ///< The NVS value used to select the AFU Delegate (FPGA, ASE, or SWSim).
   btWSSize             m_WSRequestLen;   ///< Requested size of the AFU Context workspace in bytes.
}; //CMyApp

/// @} group splapp3

////////////////////////////////////////////////////////////////////////////////
BEGIN_C_DECLS

struct CMyCmdLine
{
   btUIntPtr          flags;
#define MY_CMD_FLAG_HELP      0x00000001
#define MY_CMD_FLAG_VERSION   0x00000002
#define MY_CMD_FLAG_DEEPSCRUB 0x00000004
#define MY_CMD_FLAG_SEED      0x00000008

   std::string        AFUTarget;
   btInt              LogLevel;
   btUnsigned32bitInt Seed;
};

struct CMyCmdLine gMyCmdLine =
{
   0,
   std::string(DEFAULT_TARGET_AFU),
   LOG_INFO,
   0
};

int my_on_nix_long_option_only(AALCLP_USER_DEFINED , const char * );
int my_on_nix_long_option(AALCLP_USER_DEFINED , const char * , const char * );

aalclp_option_only my_nix_long_option_only = { my_on_nix_long_option_only, };
aalclp_option      my_nix_long_option      = { my_on_nix_long_option,      };

void help_msg_callback(FILE * , struct _aalclp_gcs_compliance_data * );
void showhelp(FILE * , struct _aalclp_gcs_compliance_data * );

AALCLP_DECLARE_GCS_COMPLIANT(stdout,
                             "splapp3",
                             "0.0.0",
                             "",
                             help_msg_callback,
                             &gMyCmdLine)

int parsecmds(struct CMyCmdLine * , int , char *[] );
int verifycmds(struct CMyCmdLine * );
END_C_DECLS

////////////////////////////////////////////////////////////////////////////////
// Forward declarations for non-command-line-parsing utility functions

void _DumpCL( void         *pCL,  // pointer to cache-line to print
             ostringstream &oss);  // add it to this ostringstream
void Show2CLs( void          *pCLExpected, // pointer to cache-line expected
               void          *pCLFound,    // pointer to found cache line
               ostringstream &oss);         // add it to this ostringstream

////////////////////////////////////////////////////////////////////////////////


//=============================================================================
// Name:          main
// Description:   Entry point to the application
// Inputs:        arc, argv
// Outputs:       returns number of errors
// Comments:      Main initializes the system and tracks state as it runs
//                through the protocol.
//=============================================================================
int main(int argc, char *argv[])
{
   ////////////////////////////////////////////////////////////////////////////
   // Get the arguments

   btInt res = 0;

   if ( argc < 2 ) {
      showhelp(stdout, &_aalclp_gcs_data);
      return 1;
   } else if ( parsecmds(&gMyCmdLine, argc, argv) ) {
      cerr << "Error scanning command line." << endl;
      return 2;
   } else if ( flag_is_set(gMyCmdLine.flags, MY_CMD_FLAG_HELP|MY_CMD_FLAG_VERSION) ) {
      return 0; // per GCS
   } else if ( verifycmds(&gMyCmdLine) ) {
      return 3;
   }

   cerr << "======================" << endl;
   cerr << " AAL SPL VAFU Sample 3"  << endl;
   cerr << "======================" << endl << endl;

#if DBG_HOOK
   cout << "Waiting for debugger attach.." << endl;
   while ( gWaitForDebuggerAttach ) {
      SleepSec(1);
   }
   // Init the AAL logger.
   pAALLogger()->AddToMask(LM_All, 8); // All subsystems
   pAALLogger()->SetDestination(ILogger::CERR);
#else
   if ( gMyCmdLine.LogLevel > 0 ) {
      pAALLogger()->AddToMask(LM_All, gMyCmdLine.LogLevel);
      pAALLogger()->SetDestination(ILogger::CERR);
   }
#endif // DBG_HOOK

   bool              bStarted;      // Tracks if the runtime and service are initialized
   CMyApp            myapp;         // SPL AFU Client. Also a CSyncClient.

   ////////////////////////////////////////////////////////////////////////////
   // Store the command line options into the myapp object for use later
   myapp.AFUTarget(gMyCmdLine.AFUTarget);

   ////////////////////////////////////////////////////////////////////////////
   // Define the startup parameters of the Runtime.
   // These are, in general, a dependent on what kinds of Services you will be
   //    loading and accessing.
   // For example, software-only services can be loaded via the default broker,
   //    but hardware-based services typically take something more, e.g. a
   //    broker that understands the underlying hardware resources.
   // THIS CODE IS SUBJECT TO CHANGE.

   NamedValueSet RunTimeArgs;          // Used to initialize the Runtim
   if ( (0 == myapp.AFUTarget().compare(SPLAFU_NVS_VAL_TARGET_ASE)) ||
        (0 == myapp.AFUTarget().compare(SPLAFU_NVS_VAL_TARGET_SWSIM)) ) {
      RunTimeArgs.Add(SYSINIT_KEY_SYSTEM_NOKERNEL, true);
   } else {
      NamedValueSet ConfigRecord;
      ConfigRecord.Add(XLRUNTIME_CONFIG_BROKER_SERVICE, "librrmbroker");
      RunTimeArgs.Add(XLRUNTIME_CONFIG_RECORD, ConfigRecord);
   }

   ////////////////////////////////////////////////////////////////////////////
   // Define the Manifest, which selects which Service is to be obtained.
   // NOTE: This example is bypassing the Resource Manager's configuration record lookup
   //  mechanism.  This code is work around code and subject to change.

   btcString AFUName = "SPLAFU";
   NamedValueSet Manifest(SPLAFU_MANIFEST);
   Manifest.Add(AAL_FACTORY_CREATE_SERVICENAME, AFUName);
   Manifest.Add(SPLAFU_NVS_KEY_TARGET, myapp.AFUTarget().c_str());

   ////////////////////////////////////////////////////////////////////////////
   // Start up the runtime and get the service.
#if DBG_HOOK
   INFO("RunTimeArgs: " << RunTimeArgs);
   INFO("Manifest: " << Manifest);
#endif // DBG_HOOK

   bStarted = myapp.start( RunTimeArgs, Manifest);
   if (!bStarted) {
      myapp.syncStop();
      return 4;
   }

   ////////////////////////////////////////////////////////////////////////////
   // Get a big buffer that will contain 3 items:
   // 1) VAFU_CNTXT is a command parameter block instructing AFU what to do, and
   //    providing a place for AFU to respond when it is finished doing it.
   // 2) Source buffer of copy_buf_len length
   // 3) Destination buffer of copy_buf_len length

   // Set copy_buf_len based on target. Default small buffer for ASE and SW Sim, bit for HW.
   btWSSize copy_buf_len = GB(1)-CL(1);

   // Allocate the buffer, and expose the virtual address and length for the general case
   myapp.syncWorkspaceAllocate( sizeof(VAFU2_CNTXT) + copy_buf_len + copy_buf_len,
      TransactionID());

   btVirtAddr         pWSUsrVirt = myapp.OneLargeVirt(); // Address of Workspace
   const btWSSize     WSLen      = myapp.OneLargeSize(); // Length of workspace

   INFO("Allocated " << WSLen << "-byte Workspace at virtual address "
                     << std::hex << (void *)pWSUsrVirt);

   // Number of bytes in each of the source and destination buffers (4 MiB in this case)
   btUnsigned32bitInt a_num_bytes= (btUnsigned32bitInt) ((WSLen - sizeof(VAFU2_CNTXT)) / 2);
   btUnsigned32bitInt a_num_cl   = 1 << atoi(argv[2]);  // number of cache lines in buffer

   // VAFU Context is at the beginning of the buffer
   VAFU2_CNTXT       *pVAFU2_cntxt = reinterpret_cast<VAFU2_CNTXT *>(pWSUsrVirt);

   // The source buffer is right after the VAFU Context
   btVirtAddr         pSource = pWSUsrVirt + sizeof(VAFU2_CNTXT);

   // The destination buffer is right after the source buffer
   btVirtAddr         pDest   = pSource + a_num_bytes;

   struct OneCL {                      // Make a cache-line sized structure
      btUnsigned32bitInt dw[16];       //    for array arithmetic
   };
   struct OneCL      *pSourceCL = reinterpret_cast<struct OneCL *>(pSource);
   struct OneCL      *pDestCL   = reinterpret_cast<struct OneCL *>(pDest);

   // Note: the usage of the VAFU2_CNTXT structure here is specific to the underlying bitstream
   // implementation. The bitstream targeted for use with this sample application must implement
   // the Validation AFU 2 interface and abide by the contract that a VAFU2_CNTXT structure will
   // appear at byte offset 0 within the supplied AFU Context workspace.

   // Initialize the command buffer
   ::memset(pVAFU2_cntxt, 0, sizeof(VAFU2_CNTXT));
   pVAFU2_cntxt->num_cl  = a_num_cl;
   pVAFU2_cntxt->pSource = pSource;
   pVAFU2_cntxt->pDest   = pDest;

   INFO("VAFU2 Context=" << std::hex << (void *)pVAFU2_cntxt <<
        " Src="          << std::hex << (void *)pVAFU2_cntxt->pSource <<
        " Dest="         << std::hex << (void *)pVAFU2_cntxt->pDest << std::dec);
   INFO("Cache lines in each buffer="  << std::dec << pVAFU2_cntxt->num_cl <<
        " (bytes="       << std::dec << pVAFU2_cntxt->num_cl * CL(1) <<
        " 0x"            << std::hex << pVAFU2_cntxt->num_cl * CL(1) << std::dec << ")");

   // Init the src/dest buffers, based on the desired sequence (either fixed or random).
   INFO("Initializing buffers with fixed data pattern. (src=0xafafafaf dest=0xbebebebe)");

   ::memset( pSource, 0xAF, a_num_bytes );
   ::memset( pDest,   0xBE, a_num_bytes );

   // Buffers have been initialized
   ////////////////////////////////////////////////////////////////////////////

   ////////////////////////////////////////////////////////////////////////////
   // Get the AFU and start talking to it

   // Acquire the AFU. Once acquired in a TransactionContext, can issue CSR Writes and access DSM.
   // Provide a workspace and so also start the task.
   // The VAFU2 Context is assumed to be at the start of the workspace.
   INFO("Starting SPL Transaction with Workspace");
   myapp.syncStartTransactionContext(TransactionID(), pWSUsrVirt, 100);

   // [OPTIONAL]
   // Examine the AFU ID from the AFU DSM pointer returned in the response event.
   volatile VAFU2_DSM *pAFUDSM = (volatile VAFU2_DSM *)myapp.AFUDSMVirt();
   ASSERT(pAFUDSM != NULL);
   INFO("AFU ID = 0x" << std::hex << pAFUDSM->vafu2.AFU_ID[1] <<
        " 0x" << std::hex << pAFUDSM->vafu2.AFU_ID[0] << std::dec);

#if 0  /* not working with ASE yet */
   // [OPTIONAL]
   // Verify that the CSR write region was mapped properly.
   // To do so, we..
   // 1) clear AFU_DSM_SCRATCH to zero.
   // 2) write some non-zero value to AFU_CSR_SCRATCH.
   // 3) verify that the value is reflected at AFU_DSM_SCRATCH.

   INFO("(before clearing) AFU_DSM_SCRATCH is " <<
        std::hex << pAFUDSM->AFU_DSM_SCRATCH << std::dec);

   pAFUDSM->AFU_DSM_SCRATCH = 0;
   INFO("(after clearing) AFU_DSM_SCRATCH is " << std::hex << pAFUDSM->AFU_DSM_SCRATCH << std::dec);

   btBool bRes = myapp.CSRWrite(byte_offset_AFU_CSR_SCRATCH / 4, 0xdecafbad);
   ASSERT(bRes);
   INFO("CSRWrite() returned " << bRes);

   INFO("(when checking) AFU_DSM_SCRATCH is " << std::hex << pAFUDSM->AFU_DSM_SCRATCH << std::dec);
   ASSERT(0xdecafbad == pAFUDSM->AFU_DSM_SCRATCH);
#endif /* 0 */

   // Done with OPTIONAL talking to the AFU
   ////////////////////////////////////////////////////////////////////////////

   // Check the status of starting
   if ( !myapp.IsOK() ) {
      ERR("IsOK check failed");
      return 1;
   }
   // The AFU is running
   ////////////////////////////////////////////////////////////////////////////

   ////////////////////////////////////////////////////////////////////////////
   // Wait for the AFU to be done. This is AFU-specific, we have chosen to poll ...

   // Set timeout increment based on hardware, software, or simulation
   bt32bitInt count(6000);  // 60 seconds with 10 millisecond sleep
   bt32bitInt delay(10);   // 10 milliseconds is the default
   if ( 0 == myapp.AFUTarget().compare(SPLAFU_NVS_VAL_TARGET_ASE) ) {
      delay = 1000;        // 1 second polling loop for RTL simulation
      count = 7200;        // two hour timeout
   }

   // Wait for SPL VAFU to finish code
   volatile bt32bitInt done = pVAFU2_cntxt->Status & VAFU2_CNTXT_STATUS_DONE;
   while (!done && --count) {
      SleepMilli( delay );
      done = pVAFU2_cntxt->Status & VAFU2_CNTXT_STATUS_DONE;
   }
   if ( !done ) {
      // must have dropped out of loop due to count -- never saw update
      ERR("AFU never signaled it was done. Timing out anyway. Results may be strange.\n");
   }
   // The AFU is done
   ////////////////////////////////////////////////////////////////////////////

   ////////////////////////////////////////////////////////////////////////////
   // OPTIONAL: Check performance counters on hardware

   // only do the performance counters for the real FPGA. Not defined in other modes.
   if ( done ) {
      // Print performance counters
      INFO("FPGA Clocks of read hit latency     = 0x" << hex << pAFUDSM->rsvd1[1] <<
           " "                               << dec << pAFUDSM->rsvd1[1]);
      INFO("FPGA Clocks of read hit bandwidth   = 0x" << hex << pAFUDSM->rsvd2[1] <<
           " "                               << dec << pAFUDSM->rsvd2[1]);
      INFO("FPGA Clocks of read miss latency    = 0x" << hex << pAFUDSM->rsvd1[0] <<
           " "                               << dec << pAFUDSM->rsvd1[0]);
      INFO("FPGA Clocks to read miss bandwidth  = 0x" << hex << pAFUDSM->rsvd2[0] <<
           " "                               << dec << pAFUDSM->rsvd2[0]);
      INFO("FPGA Clocks of write hit latency    = 0x" << hex << pAFUDSM->rsvd1[3] <<
           " "                               << dec << pAFUDSM->rsvd1[3]);
      INFO("FPGA Clocks of write hit bandwidth  = 0x" << hex << pAFUDSM->rsvd2[3] <<
           " "                               << dec << pAFUDSM->rsvd2[3]);
      INFO("FPGA Clocks of write miss latency   = 0x" << hex << pAFUDSM->rsvd1[2] <<
           " "                               << dec << pAFUDSM->rsvd1[2]);
      INFO("FPGA Clocks to write miss bandwidth = 0x" << hex << pAFUDSM->rsvd2[2] <<
           " "                               << dec << pAFUDSM->rsvd2[2]);
      INFO("");
      INFO("FPGA Clock is 200 MHz, or takes 5 ns.");
      INFO("read miss latency    = " << 5.0*pAFUDSM->rsvd1[0]/((double)a_num_cl) << " ns.");

      INFO("");
      double num_bytes = (double)a_num_cl * CL(1);
      const double billion = 1000.0 * 1000.0 * 1000.0 ;
      INFO("Bandwidth = #bytes moved/time.\n" <<
            "\t#bytes moved is " << num_bytes);
      INFO("read miss bandwidth  = " << num_bytes/(5.0*pAFUDSM->rsvd2[0]) << " GB/s.");
      INFO("write miss bandwidth = " << num_bytes/(5.0*pAFUDSM->rsvd2[2]) << " GB/s.");
   } // performance counters for FPGA

   // Done with Performance Counters
   ////////////////////////////////////////////////////////////////////////////

   ////////////////////////////////////////////////////////////////////////////
   // Stop the AFU

   // Issue Stop Transaction and wait for OnTransactionStopped
   INFO("Stopping SPL Transaction");
   myapp.syncStopTransactionContext( TransactionID() );
   INFO("SPL Transaction complete");

   ////////////////////////////////////////////////////////////////////////////
   // Check the buffers to make sure they copied okay

   btUnsignedInt        cl;               // Loop counter. Cache-Line number.
   int                  tres;             // If many errors in buffer, only dump a limited number
   ostringstream        oss("");          // Place to stash fancy strings
   btUnsigned32bitInt   tCacheLine[16];   // Temporary cacheline for various purposes
   CASSERT( sizeof(tCacheLine) == CL(1) );

   INFO("Verifying buffers in workspace");

   // Verify 1) that the source buffer was not corrupted and
   //        2) that the dest buffer contains the source buffer contents.

   ::memset( tCacheLine, 0xAF, sizeof(tCacheLine) );  // expected for both source and dest buffers

   tres = 0;                                          // dump only 4 CL's at a time
   for ( cl = 0 ; cl < a_num_cl && tres < 4; ++cl ) { // check for error in source buffer
      if( ::memcmp( tCacheLine, &pSourceCL[cl], CL(1) ) ) {
         Show2CLs( tCacheLine, &pSourceCL[cl], oss);
         ERR("Source cache line " << cl << " @" << (void*)&pSourceCL[cl] <<
               " has been corrupted.\n" << oss.str() );
         oss.str(std::string(""));
         ++res;
         ++tres;
      }
   }
   tres = 0;                                          // dump only 4 CL's at a time
   for ( cl = 0 ; cl < a_num_cl && tres < 4; ++cl ) { // check for error in destination buffer
      if( ::memcmp( tCacheLine, &pDestCL[cl], CL(1) ) ) {
         Show2CLs( tCacheLine, &pDestCL[cl], oss);
         ERR("Destination cache line " << cl << " @" << (void*)&pDestCL[cl] <<
               " is not what was expected.\n" << oss.str() );
         oss.str(std::string(""));
         ++res;
         ++tres;
      }
   }
   // Done Checking the buffers
   ////////////////////////////////////////////////////////////////////////////

   ////////////////////////////////////////////////////////////////////////////
   // Clean up and exit

   INFO("Workspace verification complete, freeing workspace.");
   myapp.syncWorkspaceFree( pWSUsrVirt, TransactionID());

   INFO("Releasing the SPL Service");
   myapp.syncRelease(TransactionID());

   INFO("Stopping the XL Runtime");
   myapp.stop();

   if ( res > 0 ) {
      ERR("Test FAILED with " << res << " error" << ((res > 1) ? "s." : "."));
   } else {
      INFO("Test PASSED");
   }

   return res;
}  // main


///////////////////////////////////////////////////////////////////////////////
// Utility functions


#if defined ( __AAL_WINDOWS__ )
# define strcasecmp _stricmp
#endif // __AAL_WINDOWS__


BEGIN_C_DECLS

int my_on_nix_long_option_only(AALCLP_USER_DEFINED user, const char *option)
{
   struct CMyCmdLine *cl = (struct CMyCmdLine *)user;

   if ( 0 == strcmp("--help", option) ) {
      flag_setf(cl->flags, MY_CMD_FLAG_HELP);
   } else if ( 0 == strcmp("--version", option) ) {
      flag_setf(cl->flags, MY_CMD_FLAG_VERSION);
   } else if ( 0 == strcmp("--deep-scrub", option) ) {
      flag_setf(cl->flags, MY_CMD_FLAG_DEEPSCRUB);
   }

   return 0;
}

int my_on_nix_long_option(AALCLP_USER_DEFINED user, const char *option, const char *value)
{
   struct CMyCmdLine *cl     = (struct CMyCmdLine *)user;
   char              *endptr = NULL;

   if ( 0 == strcmp("--target", option) ) {
      if ( 0 == strcasecmp("fpga", value) ) {
         cl->AFUTarget = std::string(SPLAFU_NVS_VAL_TARGET_FPGA);
      } else if ( 0 == strcasecmp("ase", value) ) {
         cl->AFUTarget = std::string(SPLAFU_NVS_VAL_TARGET_ASE);
      } else if ( 0 == strcasecmp("swsim", value) ) {
         cl->AFUTarget = std::string(SPLAFU_NVS_VAL_TARGET_SWSIM);
      } else {
         cout << "Invalid value for --target : " << value << endl;
         return 4;
      }
   } else if ( 0 == strcmp("--log", option) ) {
      cl->LogLevel = (btInt)strtol(value, &endptr, 0);
      if ( endptr != value + strlen(value) ) {
         cl->LogLevel = 0;
      } else if ( cl->LogLevel < 0) {
         cl->LogLevel = 0;
      } else if ( cl->LogLevel > 8) {
         cl->LogLevel = 8;
      }
   } else if ( 0 == strcmp("--seed", option) ) {
      cl->Seed = (btUnsigned32bitInt)strtoul(value, &endptr, 0);
      if ( endptr != value + strlen(value) ) {
         cout << "Invalid value for --seed : " << value << endl;
         return 5;
      }
   }
   return 0;
}

void help_msg_callback(FILE *fp, struct _aalclp_gcs_compliance_data *gcs)
{
   fprintf(fp, "Usage:\n");
   fprintf(fp, "   splapp [--target=<TARGET>] [--seed=<SEED>] [--deep-scrub]\n");
   fprintf(fp, "\n");
   fprintf(fp, "      <TARGET>     = one of { fpga ase swsim }\n");
   fprintf(fp, "      <SEED>       = 32 bit seed for RNG / fixed pattern\n");
   fprintf(fp, "      --deep-scrub = run thorough permutation testing (default is basic checkout)\n");
   fprintf(fp, "\n");
}

void showhelp(FILE *fp, struct _aalclp_gcs_compliance_data *gcs)
{
   help_msg_callback(fp, gcs);
}

int parsecmds(struct CMyCmdLine *cl, int argc, char *argv[])
{
   int    res;
   int    clean;
   aalclp clp;

   res = aalclp_init(&clp);
   if ( 0 != res ) {
      cerr << "aalclp_init() failed : " << res << ' ' << strerror(res) << endl;
      return res;
   }

   my_nix_long_option_only.user = cl;
   aalclp_add_nix_long_option_only(&clp, &my_nix_long_option_only);

   my_nix_long_option.user = cl;
   aalclp_add_nix_long_option(&clp, &my_nix_long_option);

   res = aalclp_add_gcs_compliance(&clp);
   if ( 0 != res ) {
      cerr << "aalclp_add_gcs_compliance() failed : " << res << ' ' << strerror(res) << endl;
      goto CLEANUP;
   }

   res = aalclp_scan_argv(&clp, argc, argv);
   if ( 0 != res ) {
      cerr << "aalclp_scan_argv() failed : " << res << ' ' << strerror(res) << endl;
   }

CLEANUP:
   clean = aalclp_destroy(&clp);
   if ( 0 != clean ) {
      cerr << "aalclp_destroy() failed : " << clean << ' ' << strerror(clean) << endl;
   }

   return res;
}

int verifycmds(struct CMyCmdLine *cl)
{
   return 0;
}

END_C_DECLS


////////////////////////////////////////////////////////////////////////////////
// Other utility functions

/// @addtogroup splapp3
/// @{

void _DumpCL( void         *pCL,  // pointer to cache-line to print
             ostringstream &oss)  // add it to this ostringstream
{
   oss << std::hex << std::setfill('0') << std::uppercase;
   btUnsigned32bitInt *pu32 = reinterpret_cast<btUnsigned32bitInt*>(pCL);
   for( int i = 0; i < ( CL(1) / sizeof(btUnsigned32bitInt)); ++i ) {
      oss << "0x" << std::setw(8) << *pu32 << " ";
      ++pu32;
   }
   oss << std::nouppercase;
}  // _DumpCL

void Show2CLs( void          *pCLExpected, // pointer to cache-line expected
               void          *pCLFound,    // pointer to found cache line
               ostringstream &oss)         // add it to this ostringstream
{
   oss << "Expected: ";
   _DumpCL( pCLExpected, oss);
   oss << "\n";
   oss << "Found:    ";
   _DumpCL( pCLFound, oss);
//   oss << "\n";    /* no terminating linefeed, macro at end will add it. */
}  // _DumpCL

/// @} group splapp3

// End Utility functions
///////////////////////////////////////////////////////////////////////////////

/**
@addtogroup splapp3
@{

@verbatim
This application is for example purposes only.
It is not intended to represent a model for developing commercially-deployable applications.
It is designed to show working examples of the AAL programming model and APIs.@endverbatim

This Sample demonstrates the following:

<ul>
  <li>An ISPLClient implementation similar to that in splapp2.</li>
  <li>Use of the CSyncClient super-class to inherit implementation.</li>
  <li>Runtime selection of AFU targets with SPLAFU.</li>
  <li>SPL transactions with ISPLAFU.</li>
  <li>All of the irrelevant (to the coding example) mutability available in splapp and splapp2 removed, leaving just the raw protocol.</li>
</ul>

This sample is designed to be used with SPLAFU.

1 Summary of Operation

splapp3 relies on its instantiation of CSyncClient inherited by CMyApp to
perform the brunt of the XL runtime interaction. CSyncClient instantiates
a instance of the XL Runtime object, and provides default operations for the
IRuntime and IServiceClient interfaces. CMyApp inherits this implementation
and extends it to add the SPL-specific ISPLClient implementation and a synchronous
version of the ISPLAFU Service interface.

The CMyApp object declared in main() handles all of these functions, hopefully leaving
the bulk of the interesting processing to be exposed cleanly in main().

The command line parameters are parsed and then stored in the CMyApp instance, where they
are used to select the AFU target implementation, whether to run permutation testing,
and to save the requested random seed value, if any, for random source buffer initialization.

Some AFU-specific Runtime parameter configuration is performed prior to calling
CMyApp's start() function, which in turn calls the Runtime.start() function, handles the
response in runtimeStarted(), and then calls synAllocService to instantiate the
SPL Service, which is again serviced in CSyncClient::serviceAllocated(). After all of this
CMyAPP.start() returns with an error code set if anything went wrong.

The SPL test parameters are set up and the test(s) is/are performed.

When the SPL test(s) is(are) complete, syncRelease() and finally stop() are called to shut down
all the machinery. Everything is synchronous behind the scenes. The CMyApp class could be
re-used, although probably the simpler form in splapp3 should be made canonical and then
extended for the additional functionality provided in splapp2.

Finally, the SPL test status is reported, and the application exits.

2 Running the application

2.0 Online Help

@code
$ splapp3 --help
Usage:
   splapp3 [--target=<TARGET>] [--seed=<SEED>] [--deep-scrub] [--log=<LOG_LEVEL>]

      <TARGET>     = one of { fpga ase swsim }
      <SEED>       = 32 bit seed for RNG / fixed pattern
      <LOG_LEVEL>  = 0 to 8, with 0 being unwise and 8 being excruciatingly verbose.
                     Default is 5.
@endcode

2.1 SPL FPGA (HWSPLAFU)

Prerequisites for running the sample with an FPGA:
<ul>
  <li>The SPL AAL device drivers must be loaded.</li>
  <li>The AAL Resource Manager must be running.</li>
  <li>The FPGA module connected to the system must be programmed with an appropriate SPL AFU bit stream.</li>
</ul>

@code
$ splapp3 --target=fpga@endcode

2.2 SPL AFU Simulation Environment (ASESPLAFU)

Prerequisites for running the sample with ASE:
<ul>
  <li>The ASE simulation-side application must be running on the system.</li>
</ul>

@code
$ splapp3 --target=ase@endcode

2.3 SPL Software Simulation (SWSimSPLAFU)

Prerequisites for running the sample with Software Simulation:
<ul>
  <li>(none)
</ul>

@code
$ splapp3 --target=swsim@endcode

@} group splapp3
*/



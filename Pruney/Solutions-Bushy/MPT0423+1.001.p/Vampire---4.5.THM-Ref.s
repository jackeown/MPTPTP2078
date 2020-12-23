%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0423+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:57 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 257 expanded)
%              Number of leaves         :   12 (  56 expanded)
%              Depth                    :   22
%              Number of atoms          :  200 ( 624 expanded)
%              Number of equality atoms :   78 ( 267 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1750,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1749,f26])).

fof(f26,plain,(
    k1_tarski(k1_xboole_0) != k7_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_tarski(k1_xboole_0)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k7_setfam_1(X0,X1) != k1_tarski(k1_xboole_0)
      & k1_tarski(X0) = X1
      & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
       => ( k1_tarski(X0) = X1
         => k7_setfam_1(X0,X1) = k1_tarski(k1_xboole_0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( k1_tarski(X0) = X1
       => k7_setfam_1(X0,X1) = k1_tarski(k1_xboole_0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_setfam_1)).

fof(f1749,plain,(
    k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f1745,f147])).

fof(f147,plain,(
    r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f146,f119])).

fof(f119,plain,(
    k1_xboole_0 = k3_subset_1(sK0,sK0) ),
    inference(backward_demodulation,[],[f112,f118])).

fof(f118,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(resolution,[],[f113,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f113,plain,(
    r1_tarski(sK0,sK0) ),
    inference(resolution,[],[f106,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f106,plain,(
    m1_subset_1(sK0,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f75,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

fof(f75,plain,(
    r2_hidden(sK0,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f63,f55])).

fof(f55,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK1,X1)
      | r2_hidden(sK0,X1) ) ),
    inference(superposition,[],[f37,f25])).

fof(f25,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f63,plain,(
    r1_tarski(sK1,k1_zfmisc_1(sK0)) ),
    inference(resolution,[],[f24,f45])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f112,plain,(
    k3_subset_1(sK0,sK0) = k4_xboole_0(sK0,sK0) ),
    inference(resolution,[],[f106,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f146,plain,(
    r2_hidden(k3_subset_1(sK0,sK0),k7_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f82,f53])).

fof(f53,plain,(
    r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f52,f25])).

fof(f52,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f82,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f81,f64])).

fof(f64,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,sK1)
      | m1_subset_1(X3,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f24,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f81,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK1))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f80,f57])).

fof(f57,plain,(
    m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0))) ),
    inference(resolution,[],[f24,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f80,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK1))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f77,f24])).

fof(f77,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(k7_setfam_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X1),k7_setfam_1(sK0,sK1))
      | ~ r2_hidden(X1,sK1) ) ),
    inference(superposition,[],[f48,f56])).

fof(f56,plain,(
    sK1 = k7_setfam_1(sK0,k7_setfam_1(sK0,sK1)) ),
    inference(resolution,[],[f24,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ r2_hidden(X3,k7_setfam_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | r2_hidden(k3_subset_1(X0,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k7_setfam_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) )
                | ~ m1_subset_1(X3,k1_zfmisc_1(X0)) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( k7_setfam_1(X0,X1) = X2
          <=> ! [X3] :
                ( m1_subset_1(X3,k1_zfmisc_1(X0))
               => ( r2_hidden(X3,X2)
                <=> r2_hidden(k3_subset_1(X0,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_setfam_1)).

fof(f1745,plain,
    ( ~ r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f1744])).

fof(f1744,plain,
    ( ~ r2_hidden(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | k1_xboole_0 != k1_xboole_0
    | k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1) ),
    inference(superposition,[],[f41,f1661])).

fof(f1661,plain,(
    k1_xboole_0 = sK3(k1_xboole_0,k7_setfam_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1660,f26])).

fof(f1660,plain,
    ( k1_xboole_0 = sK3(k1_xboole_0,k7_setfam_1(sK0,sK1))
    | k1_tarski(k1_xboole_0) = k7_setfam_1(sK0,sK1) ),
    inference(equality_resolution,[],[f1532])).

fof(f1532,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = sK3(X0,k7_setfam_1(sK0,sK1))
      | k1_tarski(X0) = k7_setfam_1(sK0,sK1) ) ),
    inference(equality_factoring,[],[f755])).

fof(f755,plain,(
    ! [X3] :
      ( k1_xboole_0 = sK3(X3,k7_setfam_1(sK0,sK1))
      | sK3(X3,k7_setfam_1(sK0,sK1)) = X3
      | k7_setfam_1(sK0,sK1) = k1_tarski(X3) ) ),
    inference(forward_demodulation,[],[f751,f119])).

fof(f751,plain,(
    ! [X3] :
      ( k3_subset_1(sK0,sK0) = sK3(X3,k7_setfam_1(sK0,sK1))
      | k7_setfam_1(sK0,sK1) = k1_tarski(X3)
      | sK3(X3,k7_setfam_1(sK0,sK1)) = X3 ) ),
    inference(duplicate_literal_removal,[],[f750])).

fof(f750,plain,(
    ! [X3] :
      ( k3_subset_1(sK0,sK0) = sK3(X3,k7_setfam_1(sK0,sK1))
      | k7_setfam_1(sK0,sK1) = k1_tarski(X3)
      | sK3(X3,k7_setfam_1(sK0,sK1)) = X3
      | sK3(X3,k7_setfam_1(sK0,sK1)) = X3
      | k7_setfam_1(sK0,sK1) = k1_tarski(X3) ) ),
    inference(superposition,[],[f202,f605])).

fof(f605,plain,(
    ! [X5] :
      ( sK0 = k3_subset_1(sK0,sK3(X5,k7_setfam_1(sK0,sK1)))
      | sK3(X5,k7_setfam_1(sK0,sK1)) = X5
      | k7_setfam_1(sK0,sK1) = k1_tarski(X5) ) ),
    inference(resolution,[],[f367,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK0 = X0 ) ),
    inference(superposition,[],[f50,f25])).

fof(f50,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f367,plain,(
    ! [X0] :
      ( r2_hidden(k3_subset_1(sK0,sK3(X0,k7_setfam_1(sK0,sK1))),sK1)
      | k1_tarski(X0) = k7_setfam_1(sK0,sK1)
      | sK3(X0,k7_setfam_1(sK0,sK1)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f366])).

fof(f366,plain,(
    ! [X0] :
      ( r2_hidden(k3_subset_1(sK0,sK3(X0,k7_setfam_1(sK0,sK1))),sK1)
      | k1_tarski(X0) = k7_setfam_1(sK0,sK1)
      | sK3(X0,k7_setfam_1(sK0,sK1)) = X0
      | k1_tarski(X0) = k7_setfam_1(sK0,sK1) ) ),
    inference(resolution,[],[f206,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | sK3(X0,X1) = X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f206,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0,k7_setfam_1(sK0,sK1)),k7_setfam_1(sK0,sK1))
      | r2_hidden(k3_subset_1(sK0,sK3(X0,k7_setfam_1(sK0,sK1))),sK1)
      | k1_tarski(X0) = k7_setfam_1(sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f199,f41])).

fof(f199,plain,(
    ! [X0] :
      ( sK3(X0,k7_setfam_1(sK0,sK1)) = X0
      | k1_tarski(X0) = k7_setfam_1(sK0,sK1)
      | r2_hidden(k3_subset_1(sK0,sK3(X0,k7_setfam_1(sK0,sK1))),sK1)
      | ~ r2_hidden(sK3(X0,k7_setfam_1(sK0,sK1)),k7_setfam_1(sK0,sK1)) ) ),
    inference(resolution,[],[f124,f101])).

fof(f101,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X1),sK1)
      | ~ r2_hidden(X1,k7_setfam_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f90,f24])).

fof(f90,plain,(
    ! [X1] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
      | r2_hidden(k3_subset_1(sK0,X1),sK1)
      | ~ r2_hidden(X1,k7_setfam_1(sK0,sK1)) ) ),
    inference(resolution,[],[f57,f48])).

fof(f124,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0,k7_setfam_1(sK0,sK1)),k1_zfmisc_1(sK0))
      | sK3(X0,k7_setfam_1(sK0,sK1)) = X0
      | k1_tarski(X0) = k7_setfam_1(sK0,sK1) ) ),
    inference(resolution,[],[f99,f40])).

fof(f99,plain,(
    ! [X5] :
      ( ~ r2_hidden(X5,k7_setfam_1(sK0,sK1))
      | m1_subset_1(X5,k1_zfmisc_1(sK0)) ) ),
    inference(resolution,[],[f57,f42])).

fof(f202,plain,(
    ! [X3] :
      ( sK3(X3,k7_setfam_1(sK0,sK1)) = k3_subset_1(sK0,k3_subset_1(sK0,sK3(X3,k7_setfam_1(sK0,sK1))))
      | k7_setfam_1(sK0,sK1) = k1_tarski(X3)
      | sK3(X3,k7_setfam_1(sK0,sK1)) = X3 ) ),
    inference(resolution,[],[f124,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | sK3(X0,X1) != X0
      | k1_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f1])).

%------------------------------------------------------------------------------

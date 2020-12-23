%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:40 EST 2020

% Result     : Theorem 3.88s
% Output     : Refutation 3.88s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 698 expanded)
%              Number of leaves         :   15 ( 169 expanded)
%              Depth                    :   35
%              Number of atoms          :  172 (1537 expanded)
%              Number of equality atoms :   85 ( 593 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10131,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9591,f75])).

fof(f75,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f9591,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f41,f9588])).

fof(f9588,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f9586,f9197])).

fof(f9197,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f8967])).

fof(f8967,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k4_xboole_0(sK1,sK3) ),
    inference(backward_demodulation,[],[f89,f8966])).

fof(f8966,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f8965,f41])).

fof(f8965,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f8923,f474])).

fof(f474,plain,(
    ! [X7] : k3_xboole_0(X7,X7) = X7 ),
    inference(resolution,[],[f469,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f469,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(subsumption_resolution,[],[f459,f41])).

fof(f459,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f454,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f454,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0)) ),
    inference(forward_demodulation,[],[f447,f326])).

fof(f326,plain,(
    ! [X2] : k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X2,X2)) ),
    inference(forward_demodulation,[],[f307,f84])).

fof(f84,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f40,f56])).

fof(f40,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f307,plain,(
    ! [X2] : k2_zfmisc_1(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),X2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X2,X2)) ),
    inference(superposition,[],[f229,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f229,plain,(
    ! [X2,X1] : k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X2)) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f73,f84])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f447,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X0,X0))) ),
    inference(superposition,[],[f416,f45])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f416,plain,(
    ! [X6,X5] : r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X5),k2_zfmisc_1(k2_xboole_0(k2_zfmisc_1(sK0,sK1),X6),k3_xboole_0(X5,X5))) ),
    inference(resolution,[],[f337,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f337,plain,(
    ! [X12,X11] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),X12)
      | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X11),k2_zfmisc_1(X12,k3_xboole_0(X11,X11))) ) ),
    inference(superposition,[],[f66,f326])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f8923,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK1))
    | k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f8860,f5223])).

fof(f5223,plain,(
    ! [X6] :
      ( sK1 = k4_xboole_0(sK1,X6)
      | k1_xboole_0 = k4_xboole_0(sK0,sK2) ) ),
    inference(superposition,[],[f3979,f1014])).

fof(f1014,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k3_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f605,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f605,plain,(
    ! [X12,X11] : k4_xboole_0(X11,X12) = k3_xboole_0(k4_xboole_0(X11,X12),X11) ),
    inference(resolution,[],[f476,f56])).

fof(f476,plain,(
    ! [X10,X9] : r1_tarski(k4_xboole_0(X9,X10),X9) ),
    inference(resolution,[],[f469,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f3979,plain,(
    ! [X7] :
      ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
      | sK1 = k3_xboole_0(sK1,X7) ) ),
    inference(resolution,[],[f3781,f56])).

fof(f3781,plain,(
    ! [X18] :
      ( r1_tarski(sK1,X18)
      | k1_xboole_0 = k4_xboole_0(sK0,sK2) ) ),
    inference(subsumption_resolution,[],[f3761,f43])).

fof(f43,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f3761,plain,(
    ! [X18] :
      ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_xboole_0(sK0,sK2),X18))
      | k1_xboole_0 = k4_xboole_0(sK0,sK2)
      | r1_tarski(sK1,X18) ) ),
    inference(superposition,[],[f72,f3700])).

fof(f3700,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f3659,f1014])).

fof(f3659,plain,(
    ! [X3] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X3,sK2)),sK1) ),
    inference(superposition,[],[f2176,f64])).

fof(f2176,plain,(
    ! [X8,X9] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(X8,sK2),X9)) ),
    inference(resolution,[],[f2146,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f2146,plain,(
    ! [X12,X11] : r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(X11,sK2),X12)) ),
    inference(trivial_inequality_removal,[],[f2127])).

fof(f2127,plain,(
    ! [X12,X11] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(X11,sK2),X12)) ) ),
    inference(superposition,[],[f244,f917])).

fof(f917,plain,(
    ! [X17,X15,X18,X16] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X15,X16),X17),k2_zfmisc_1(X16,X18)) ),
    inference(forward_demodulation,[],[f909,f75])).

fof(f909,plain,(
    ! [X17,X15,X18,X16] : k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X15,X16),X17),k2_zfmisc_1(X16,X18)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X17,X18)) ),
    inference(superposition,[],[f73,f616])).

fof(f616,plain,(
    ! [X4,X3] : k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,X4),X4) ),
    inference(resolution,[],[f477,f58])).

fof(f477,plain,(
    ! [X12,X11] : r1_xboole_0(k4_xboole_0(X11,X12),X12) ),
    inference(resolution,[],[f469,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f244,plain,(
    ! [X4] :
      ( k1_xboole_0 != k3_xboole_0(X4,k2_zfmisc_1(sK2,sK3))
      | r1_xboole_0(k2_zfmisc_1(sK0,sK1),X4) ) ),
    inference(superposition,[],[f143,f49])).

fof(f143,plain,(
    ! [X4] :
      ( k1_xboole_0 != k3_xboole_0(k2_zfmisc_1(sK2,sK3),X4)
      | r1_xboole_0(k2_zfmisc_1(sK0,sK1),X4) ) ),
    inference(resolution,[],[f80,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f80,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k2_zfmisc_1(sK2,sK3),X0)
      | r1_xboole_0(k2_zfmisc_1(sK0,sK1),X0) ) ),
    inference(resolution,[],[f40,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f8860,plain,(
    ! [X5] : k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X5,sK3))) ),
    inference(superposition,[],[f2388,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f2388,plain,(
    ! [X8,X9] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X8,k4_xboole_0(X9,sK3))) ),
    inference(resolution,[],[f2354,f58])).

fof(f2354,plain,(
    ! [X19,X20] : r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X19,k4_xboole_0(X20,sK3))) ),
    inference(trivial_inequality_removal,[],[f2335])).

fof(f2335,plain,(
    ! [X19,X20] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X19,k4_xboole_0(X20,sK3))) ) ),
    inference(superposition,[],[f244,f918])).

fof(f918,plain,(
    ! [X21,X19,X22,X20] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X21,k4_xboole_0(X19,X20)),k2_zfmisc_1(X22,X20)) ),
    inference(forward_demodulation,[],[f910,f74])).

fof(f74,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f910,plain,(
    ! [X21,X19,X22,X20] : k3_xboole_0(k2_zfmisc_1(X21,k4_xboole_0(X19,X20)),k2_zfmisc_1(X22,X20)) = k2_zfmisc_1(k3_xboole_0(X21,X22),k1_xboole_0) ),
    inference(superposition,[],[f73,f616])).

fof(f89,plain,
    ( k1_xboole_0 != k4_xboole_0(sK1,sK3)
    | k1_xboole_0 != k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f79,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f79,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 != k4_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f39,f60])).

fof(f39,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f27])).

fof(f9586,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f9561])).

fof(f9561,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f61,f8927])).

fof(f8927,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f8860,f1014])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 = X1
      | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f41,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:37:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (5159)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (5167)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (5165)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (5157)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (5160)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (5158)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (5168)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (5155)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (5166)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (5156)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (5154)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (5153)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (5161)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (5154)Refutation not found, incomplete strategy% (5154)------------------------------
% 0.21/0.50  % (5154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (5154)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (5154)Memory used [KB]: 10618
% 0.21/0.50  % (5154)Time elapsed: 0.089 s
% 0.21/0.50  % (5154)------------------------------
% 0.21/0.50  % (5154)------------------------------
% 0.21/0.51  % (5169)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (5172)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (5162)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (5170)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (5171)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (5173)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (5173)Refutation not found, incomplete strategy% (5173)------------------------------
% 0.21/0.52  % (5173)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (5173)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (5173)Memory used [KB]: 10618
% 0.21/0.52  % (5173)Time elapsed: 0.115 s
% 0.21/0.52  % (5173)------------------------------
% 0.21/0.52  % (5173)------------------------------
% 0.21/0.53  % (5164)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (5163)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 3.88/0.88  % (5166)Refutation found. Thanks to Tanya!
% 3.88/0.88  % SZS status Theorem for theBenchmark
% 3.88/0.88  % SZS output start Proof for theBenchmark
% 3.88/0.88  fof(f10131,plain,(
% 3.88/0.88    $false),
% 3.88/0.88    inference(subsumption_resolution,[],[f9591,f75])).
% 3.88/0.88  fof(f75,plain,(
% 3.88/0.88    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.88/0.88    inference(equality_resolution,[],[f62])).
% 3.88/0.88  fof(f62,plain,(
% 3.88/0.88    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 3.88/0.88    inference(cnf_transformation,[],[f17])).
% 3.88/0.88  fof(f17,axiom,(
% 3.88/0.88    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.88/0.88    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.88/0.88  fof(f9591,plain,(
% 3.88/0.88    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 3.88/0.88    inference(backward_demodulation,[],[f41,f9588])).
% 3.88/0.88  fof(f9588,plain,(
% 3.88/0.88    k1_xboole_0 = sK0),
% 3.88/0.88    inference(subsumption_resolution,[],[f9586,f9197])).
% 3.88/0.88  fof(f9197,plain,(
% 3.88/0.88    k1_xboole_0 != k4_xboole_0(sK1,sK3)),
% 3.88/0.88    inference(trivial_inequality_removal,[],[f8967])).
% 3.88/0.88  fof(f8967,plain,(
% 3.88/0.88    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k4_xboole_0(sK1,sK3)),
% 3.88/0.88    inference(backward_demodulation,[],[f89,f8966])).
% 3.88/0.88  fof(f8966,plain,(
% 3.88/0.88    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 3.88/0.88    inference(subsumption_resolution,[],[f8965,f41])).
% 3.88/0.88  fof(f8965,plain,(
% 3.88/0.88    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 3.88/0.88    inference(forward_demodulation,[],[f8923,f474])).
% 3.88/0.88  fof(f474,plain,(
% 3.88/0.88    ( ! [X7] : (k3_xboole_0(X7,X7) = X7) )),
% 3.88/0.88    inference(resolution,[],[f469,f56])).
% 3.88/0.88  fof(f56,plain,(
% 3.88/0.88    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.88/0.88    inference(cnf_transformation,[],[f33])).
% 3.88/0.88  fof(f33,plain,(
% 3.88/0.88    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.88/0.88    inference(ennf_transformation,[],[f9])).
% 3.88/0.89  fof(f9,axiom,(
% 3.88/0.89    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.88/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.88/0.89  fof(f469,plain,(
% 3.88/0.89    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.88/0.89    inference(subsumption_resolution,[],[f459,f41])).
% 3.88/0.89  fof(f459,plain,(
% 3.88/0.89    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | r1_tarski(X0,X0)) )),
% 3.88/0.89    inference(resolution,[],[f454,f72])).
% 3.88/0.89  fof(f72,plain,(
% 3.88/0.89    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2)) )),
% 3.88/0.89    inference(cnf_transformation,[],[f38])).
% 3.88/0.89  fof(f38,plain,(
% 3.88/0.89    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 3.88/0.89    inference(ennf_transformation,[],[f18])).
% 3.88/0.89  fof(f18,axiom,(
% 3.88/0.89    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 3.88/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 3.88/0.89  fof(f454,plain,(
% 3.88/0.89    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0))) )),
% 3.88/0.89    inference(forward_demodulation,[],[f447,f326])).
% 3.88/0.89  fof(f326,plain,(
% 3.88/0.89    ( ! [X2] : (k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X2,X2))) )),
% 3.88/0.89    inference(forward_demodulation,[],[f307,f84])).
% 3.88/0.89  fof(f84,plain,(
% 3.88/0.89    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.88/0.89    inference(resolution,[],[f40,f56])).
% 3.88/0.89  fof(f40,plain,(
% 3.88/0.89    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.88/0.89    inference(cnf_transformation,[],[f27])).
% 3.88/0.89  fof(f27,plain,(
% 3.88/0.89    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.88/0.89    inference(flattening,[],[f26])).
% 3.88/0.89  fof(f26,plain,(
% 3.88/0.89    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.88/0.89    inference(ennf_transformation,[],[f23])).
% 3.88/0.89  fof(f23,negated_conjecture,(
% 3.88/0.89    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.88/0.89    inference(negated_conjecture,[],[f22])).
% 3.88/0.89  fof(f22,conjecture,(
% 3.88/0.89    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.88/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 3.88/0.89  fof(f307,plain,(
% 3.88/0.89    ( ! [X2] : (k2_zfmisc_1(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),X2) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X2,X2))) )),
% 3.88/0.89    inference(superposition,[],[f229,f64])).
% 3.88/0.89  fof(f64,plain,(
% 3.88/0.89    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 3.88/0.89    inference(cnf_transformation,[],[f20])).
% 3.88/0.89  fof(f20,axiom,(
% 3.88/0.89    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 3.88/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 3.88/0.89  fof(f229,plain,(
% 3.88/0.89    ( ! [X2,X1] : (k3_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X1),k2_zfmisc_1(k2_zfmisc_1(sK2,sK3),X2)) = k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X1,X2))) )),
% 3.88/0.89    inference(superposition,[],[f73,f84])).
% 3.88/0.89  fof(f73,plain,(
% 3.88/0.89    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 3.88/0.89    inference(cnf_transformation,[],[f21])).
% 3.88/0.89  fof(f21,axiom,(
% 3.88/0.89    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 3.88/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 3.88/0.89  fof(f447,plain,(
% 3.88/0.89    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X0),k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),k3_xboole_0(X0,X0)))) )),
% 3.88/0.89    inference(superposition,[],[f416,f45])).
% 3.88/0.89  fof(f45,plain,(
% 3.88/0.89    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.88/0.89    inference(cnf_transformation,[],[f8])).
% 3.88/0.89  fof(f8,axiom,(
% 3.88/0.89    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.88/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 3.88/0.89  fof(f416,plain,(
% 3.88/0.89    ( ! [X6,X5] : (r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X5),k2_zfmisc_1(k2_xboole_0(k2_zfmisc_1(sK0,sK1),X6),k3_xboole_0(X5,X5)))) )),
% 3.88/0.89    inference(resolution,[],[f337,f48])).
% 3.88/0.89  fof(f48,plain,(
% 3.88/0.89    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.88/0.89    inference(cnf_transformation,[],[f16])).
% 3.88/0.89  fof(f16,axiom,(
% 3.88/0.89    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.88/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.88/0.89  fof(f337,plain,(
% 3.88/0.89    ( ! [X12,X11] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),X12) | r1_tarski(k2_zfmisc_1(k2_zfmisc_1(sK0,sK1),X11),k2_zfmisc_1(X12,k3_xboole_0(X11,X11)))) )),
% 3.88/0.89    inference(superposition,[],[f66,f326])).
% 3.88/0.89  fof(f66,plain,(
% 3.88/0.89    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 3.88/0.89    inference(cnf_transformation,[],[f34])).
% 3.88/0.89  fof(f34,plain,(
% 3.88/0.89    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 3.88/0.89    inference(ennf_transformation,[],[f19])).
% 3.88/0.89  fof(f19,axiom,(
% 3.88/0.89    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 3.88/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 3.88/0.89  fof(f8923,plain,(
% 3.88/0.89    k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK1)) | k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 3.88/0.89    inference(superposition,[],[f8860,f5223])).
% 3.88/0.89  fof(f5223,plain,(
% 3.88/0.89    ( ! [X6] : (sK1 = k4_xboole_0(sK1,X6) | k1_xboole_0 = k4_xboole_0(sK0,sK2)) )),
% 3.88/0.89    inference(superposition,[],[f3979,f1014])).
% 3.88/0.89  fof(f1014,plain,(
% 3.88/0.89    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k3_xboole_0(X7,k4_xboole_0(X7,X8))) )),
% 3.88/0.89    inference(superposition,[],[f605,f49])).
% 3.88/0.89  fof(f49,plain,(
% 3.88/0.89    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.88/0.89    inference(cnf_transformation,[],[f1])).
% 3.88/0.89  fof(f1,axiom,(
% 3.88/0.89    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.88/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.88/0.89  fof(f605,plain,(
% 3.88/0.89    ( ! [X12,X11] : (k4_xboole_0(X11,X12) = k3_xboole_0(k4_xboole_0(X11,X12),X11)) )),
% 3.88/0.89    inference(resolution,[],[f476,f56])).
% 3.88/0.89  fof(f476,plain,(
% 3.88/0.89    ( ! [X10,X9] : (r1_tarski(k4_xboole_0(X9,X10),X9)) )),
% 3.88/0.89    inference(resolution,[],[f469,f68])).
% 3.88/0.89  fof(f68,plain,(
% 3.88/0.89    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 3.88/0.89    inference(cnf_transformation,[],[f35])).
% 3.88/0.89  fof(f35,plain,(
% 3.88/0.89    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.88/0.89    inference(ennf_transformation,[],[f7])).
% 3.88/0.89  fof(f7,axiom,(
% 3.88/0.89    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.88/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 3.88/0.89  fof(f3979,plain,(
% 3.88/0.89    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(sK0,sK2) | sK1 = k3_xboole_0(sK1,X7)) )),
% 3.88/0.89    inference(resolution,[],[f3781,f56])).
% 3.88/0.89  fof(f3781,plain,(
% 3.88/0.89    ( ! [X18] : (r1_tarski(sK1,X18) | k1_xboole_0 = k4_xboole_0(sK0,sK2)) )),
% 3.88/0.89    inference(subsumption_resolution,[],[f3761,f43])).
% 3.88/0.89  fof(f43,plain,(
% 3.88/0.89    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.88/0.89    inference(cnf_transformation,[],[f11])).
% 3.88/0.89  fof(f11,axiom,(
% 3.88/0.89    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.88/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.88/0.89  fof(f3761,plain,(
% 3.88/0.89    ( ! [X18] : (~r1_tarski(k1_xboole_0,k2_zfmisc_1(k4_xboole_0(sK0,sK2),X18)) | k1_xboole_0 = k4_xboole_0(sK0,sK2) | r1_tarski(sK1,X18)) )),
% 3.88/0.89    inference(superposition,[],[f72,f3700])).
% 3.88/0.89  fof(f3700,plain,(
% 3.88/0.89    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 3.88/0.89    inference(superposition,[],[f3659,f1014])).
% 3.88/0.89  fof(f3659,plain,(
% 3.88/0.89    ( ! [X3] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(X3,sK2)),sK1)) )),
% 3.88/0.89    inference(superposition,[],[f2176,f64])).
% 3.88/0.89  fof(f2176,plain,(
% 3.88/0.89    ( ! [X8,X9] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(X8,sK2),X9))) )),
% 3.88/0.89    inference(resolution,[],[f2146,f58])).
% 3.88/0.89  fof(f58,plain,(
% 3.88/0.89    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 3.88/0.89    inference(cnf_transformation,[],[f2])).
% 3.88/0.89  fof(f2,axiom,(
% 3.88/0.89    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.88/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 3.88/0.89  fof(f2146,plain,(
% 3.88/0.89    ( ! [X12,X11] : (r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(X11,sK2),X12))) )),
% 3.88/0.89    inference(trivial_inequality_removal,[],[f2127])).
% 3.88/0.89  fof(f2127,plain,(
% 3.88/0.89    ( ! [X12,X11] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(X11,sK2),X12))) )),
% 3.88/0.89    inference(superposition,[],[f244,f917])).
% 3.88/0.89  fof(f917,plain,(
% 3.88/0.89    ( ! [X17,X15,X18,X16] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X15,X16),X17),k2_zfmisc_1(X16,X18))) )),
% 3.88/0.89    inference(forward_demodulation,[],[f909,f75])).
% 3.88/0.89  fof(f909,plain,(
% 3.88/0.89    ( ! [X17,X15,X18,X16] : (k3_xboole_0(k2_zfmisc_1(k4_xboole_0(X15,X16),X17),k2_zfmisc_1(X16,X18)) = k2_zfmisc_1(k1_xboole_0,k3_xboole_0(X17,X18))) )),
% 3.88/0.89    inference(superposition,[],[f73,f616])).
% 3.88/0.89  fof(f616,plain,(
% 3.88/0.89    ( ! [X4,X3] : (k1_xboole_0 = k3_xboole_0(k4_xboole_0(X3,X4),X4)) )),
% 3.88/0.89    inference(resolution,[],[f477,f58])).
% 3.88/0.89  fof(f477,plain,(
% 3.88/0.89    ( ! [X12,X11] : (r1_xboole_0(k4_xboole_0(X11,X12),X12)) )),
% 3.88/0.89    inference(resolution,[],[f469,f69])).
% 3.88/0.89  fof(f69,plain,(
% 3.88/0.89    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 3.88/0.89    inference(cnf_transformation,[],[f35])).
% 3.88/0.89  fof(f244,plain,(
% 3.88/0.89    ( ! [X4] : (k1_xboole_0 != k3_xboole_0(X4,k2_zfmisc_1(sK2,sK3)) | r1_xboole_0(k2_zfmisc_1(sK0,sK1),X4)) )),
% 3.88/0.89    inference(superposition,[],[f143,f49])).
% 3.88/0.89  fof(f143,plain,(
% 3.88/0.89    ( ! [X4] : (k1_xboole_0 != k3_xboole_0(k2_zfmisc_1(sK2,sK3),X4) | r1_xboole_0(k2_zfmisc_1(sK0,sK1),X4)) )),
% 3.88/0.89    inference(resolution,[],[f80,f57])).
% 3.88/0.89  fof(f57,plain,(
% 3.88/0.89    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 3.88/0.89    inference(cnf_transformation,[],[f2])).
% 3.88/0.89  fof(f80,plain,(
% 3.88/0.89    ( ! [X0] : (~r1_xboole_0(k2_zfmisc_1(sK2,sK3),X0) | r1_xboole_0(k2_zfmisc_1(sK0,sK1),X0)) )),
% 3.88/0.89    inference(resolution,[],[f40,f70])).
% 3.88/0.89  fof(f70,plain,(
% 3.88/0.89    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 3.88/0.89    inference(cnf_transformation,[],[f37])).
% 3.88/0.89  fof(f37,plain,(
% 3.88/0.89    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 3.88/0.89    inference(flattening,[],[f36])).
% 3.88/0.89  fof(f36,plain,(
% 3.88/0.89    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.88/0.89    inference(ennf_transformation,[],[f13])).
% 3.88/0.89  fof(f13,axiom,(
% 3.88/0.89    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.88/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 3.88/0.89  fof(f8860,plain,(
% 3.88/0.89    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(X5,sK3)))) )),
% 3.88/0.89    inference(superposition,[],[f2388,f65])).
% 3.88/0.89  fof(f65,plain,(
% 3.88/0.89    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 3.88/0.89    inference(cnf_transformation,[],[f20])).
% 3.88/0.89  fof(f2388,plain,(
% 3.88/0.89    ( ! [X8,X9] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X8,k4_xboole_0(X9,sK3)))) )),
% 3.88/0.89    inference(resolution,[],[f2354,f58])).
% 3.88/0.89  fof(f2354,plain,(
% 3.88/0.89    ( ! [X19,X20] : (r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X19,k4_xboole_0(X20,sK3)))) )),
% 3.88/0.89    inference(trivial_inequality_removal,[],[f2335])).
% 3.88/0.89  fof(f2335,plain,(
% 3.88/0.89    ( ! [X19,X20] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X19,k4_xboole_0(X20,sK3)))) )),
% 3.88/0.89    inference(superposition,[],[f244,f918])).
% 3.88/0.89  fof(f918,plain,(
% 3.88/0.89    ( ! [X21,X19,X22,X20] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X21,k4_xboole_0(X19,X20)),k2_zfmisc_1(X22,X20))) )),
% 3.88/0.89    inference(forward_demodulation,[],[f910,f74])).
% 3.88/0.89  fof(f74,plain,(
% 3.88/0.89    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.88/0.89    inference(equality_resolution,[],[f63])).
% 3.88/0.89  fof(f63,plain,(
% 3.88/0.89    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 3.88/0.89    inference(cnf_transformation,[],[f17])).
% 3.88/0.89  fof(f910,plain,(
% 3.88/0.89    ( ! [X21,X19,X22,X20] : (k3_xboole_0(k2_zfmisc_1(X21,k4_xboole_0(X19,X20)),k2_zfmisc_1(X22,X20)) = k2_zfmisc_1(k3_xboole_0(X21,X22),k1_xboole_0)) )),
% 3.88/0.89    inference(superposition,[],[f73,f616])).
% 3.88/0.89  fof(f89,plain,(
% 3.88/0.89    k1_xboole_0 != k4_xboole_0(sK1,sK3) | k1_xboole_0 != k4_xboole_0(sK0,sK2)),
% 3.88/0.89    inference(resolution,[],[f79,f60])).
% 3.88/0.89  fof(f60,plain,(
% 3.88/0.89    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 3.88/0.89    inference(cnf_transformation,[],[f6])).
% 3.88/0.89  fof(f6,axiom,(
% 3.88/0.89    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 3.88/0.89    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.88/0.89  fof(f79,plain,(
% 3.88/0.89    ~r1_tarski(sK0,sK2) | k1_xboole_0 != k4_xboole_0(sK1,sK3)),
% 3.88/0.89    inference(resolution,[],[f39,f60])).
% 3.88/0.89  fof(f39,plain,(
% 3.88/0.89    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 3.88/0.89    inference(cnf_transformation,[],[f27])).
% 3.88/0.89  fof(f9586,plain,(
% 3.88/0.89    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 3.88/0.89    inference(trivial_inequality_removal,[],[f9561])).
% 3.88/0.89  fof(f9561,plain,(
% 3.88/0.89    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 3.88/0.89    inference(superposition,[],[f61,f8927])).
% 3.88/0.89  fof(f8927,plain,(
% 3.88/0.89    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 3.88/0.89    inference(superposition,[],[f8860,f1014])).
% 3.88/0.89  fof(f61,plain,(
% 3.88/0.89    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_xboole_0 = X1 | k1_xboole_0 != k2_zfmisc_1(X0,X1)) )),
% 3.88/0.89    inference(cnf_transformation,[],[f17])).
% 3.88/0.89  fof(f41,plain,(
% 3.88/0.89    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 3.88/0.89    inference(cnf_transformation,[],[f27])).
% 3.88/0.89  % SZS output end Proof for theBenchmark
% 3.88/0.89  % (5166)------------------------------
% 3.88/0.89  % (5166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.88/0.89  % (5166)Termination reason: Refutation
% 3.88/0.89  
% 3.88/0.89  % (5166)Memory used [KB]: 6396
% 3.88/0.89  % (5166)Time elapsed: 0.444 s
% 3.88/0.89  % (5166)------------------------------
% 3.88/0.89  % (5166)------------------------------
% 3.88/0.89  % (5152)Success in time 0.525 s
%------------------------------------------------------------------------------

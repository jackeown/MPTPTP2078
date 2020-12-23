%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:26 EST 2020

% Result     : Theorem 7.99s
% Output     : Refutation 7.99s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 199 expanded)
%              Number of leaves         :   15 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :  163 ( 339 expanded)
%              Number of equality atoms :   72 ( 143 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12137,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f12136])).

fof(f12136,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f121,f11684])).

fof(f11684,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f11661,f134])).

fof(f134,plain,(
    ! [X2,X1] : k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X1,X2)) ),
    inference(resolution,[],[f94,f51])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f93,f78])).

fof(f78,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f55,f56])).

fof(f56,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f90,f48])).

fof(f48,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f43,f56])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,k6_relat_1(X0)) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f11661,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f1421,f1581])).

fof(f1581,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),k3_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f1569,f84])).

fof(f84,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f81,f47])).

fof(f47,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f81,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) ),
    inference(resolution,[],[f49,f56])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f1569,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[],[f512,f344])).

fof(f344,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X1),X0) = k3_xboole_0(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X0)) ),
    inference(forward_demodulation,[],[f337,f47])).

fof(f337,plain,(
    ! [X0,X1] : k3_xboole_0(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X0)) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0))) ),
    inference(superposition,[],[f84,f138])).

fof(f138,plain,(
    ! [X6,X5] : k6_relat_1(k7_relat_1(k6_relat_1(X6),X5)) = k7_relat_1(k6_relat_1(k6_relat_1(X5)),k7_relat_1(k6_relat_1(X6),X5)) ),
    inference(forward_demodulation,[],[f136,f78])).

fof(f136,plain,(
    ! [X6,X5] : k6_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k7_relat_1(k6_relat_1(k6_relat_1(X5)),k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) ),
    inference(resolution,[],[f94,f63])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f53,f56])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f512,plain,(
    ! [X0,X1] : k3_xboole_0(k6_relat_1(X0),X1) = k7_relat_1(k3_xboole_0(k6_relat_1(X0),X1),k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1))) ),
    inference(resolution,[],[f197,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)),X2)
      | k3_xboole_0(k6_relat_1(X0),X1) = k7_relat_1(k3_xboole_0(k6_relat_1(X0),X1),X2) ) ),
    inference(forward_demodulation,[],[f193,f162])).

fof(f162,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k3_xboole_0(k6_relat_1(X1),X2)) = k7_relat_1(k3_xboole_0(k6_relat_1(X1),X2),X0) ),
    inference(resolution,[],[f79,f56])).

fof(f79,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X3)
      | k5_relat_1(k6_relat_1(X2),k3_xboole_0(X3,X4)) = k7_relat_1(k3_xboole_0(X3,X4),X2) ) ),
    inference(resolution,[],[f55,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f193,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X2),k3_xboole_0(k6_relat_1(X0),X1))
      | ~ r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)),X2) ) ),
    inference(resolution,[],[f86,f56])).

fof(f86,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | k3_xboole_0(X2,X3) = k5_relat_1(k6_relat_1(X4),k3_xboole_0(X2,X3))
      | ~ r1_tarski(k1_relat_1(k3_xboole_0(X2,X3)),X4) ) ),
    inference(resolution,[],[f42,f50])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f1421,plain,(
    ! [X12,X13,X11] : k7_relat_1(k7_relat_1(k6_relat_1(X13),X11),k3_xboole_0(X12,X11)) = k7_relat_1(k6_relat_1(X13),k3_xboole_0(X12,X11)) ),
    inference(forward_demodulation,[],[f1406,f78])).

fof(f1406,plain,(
    ! [X12,X13,X11] : k7_relat_1(k7_relat_1(k6_relat_1(X13),X11),k3_xboole_0(X12,X11)) = k5_relat_1(k6_relat_1(k3_xboole_0(X12,X11)),k6_relat_1(X13)) ),
    inference(superposition,[],[f425,f135])).

fof(f135,plain,(
    ! [X4,X3] : k6_relat_1(k3_xboole_0(X3,X4)) = k7_relat_1(k6_relat_1(X4),k3_xboole_0(X3,X4)) ),
    inference(resolution,[],[f94,f60])).

fof(f60,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f51,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f425,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f424,f418])).

fof(f418,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(forward_demodulation,[],[f414,f78])).

fof(f414,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X0) ),
    inference(resolution,[],[f174,f56])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),k5_relat_1(X1,k6_relat_1(X2))) = k7_relat_1(k5_relat_1(X1,k6_relat_1(X2)),X0) ) ),
    inference(resolution,[],[f80,f56])).

fof(f80,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_relat_1(X7)
      | k5_relat_1(k6_relat_1(X5),k5_relat_1(X6,X7)) = k7_relat_1(k5_relat_1(X6,X7),X5)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f55,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f424,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f420,f78])).

fof(f420,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) ),
    inference(resolution,[],[f192,f56])).

fof(f192,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ) ),
    inference(forward_demodulation,[],[f188,f78])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f95,f56])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f45,f56])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f121,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f38,f78])).

fof(f38,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f34])).

fof(f34,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:45:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (768)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.51  % (762)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (756)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (757)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (752)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (753)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (753)Refutation not found, incomplete strategy% (753)------------------------------
% 0.22/0.52  % (753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (753)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (753)Memory used [KB]: 1663
% 0.22/0.52  % (753)Time elapsed: 0.115 s
% 0.22/0.52  % (753)------------------------------
% 0.22/0.52  % (753)------------------------------
% 0.22/0.53  % (777)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.53  % (770)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  % (786)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.53  % (786)Refutation not found, incomplete strategy% (786)------------------------------
% 0.22/0.53  % (786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (758)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (786)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (786)Memory used [KB]: 1663
% 0.22/0.53  % (786)Time elapsed: 0.004 s
% 0.22/0.53  % (786)------------------------------
% 0.22/0.53  % (786)------------------------------
% 0.22/0.53  % (775)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (780)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.53  % (780)Refutation not found, incomplete strategy% (780)------------------------------
% 0.22/0.53  % (780)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (780)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (780)Memory used [KB]: 10618
% 0.22/0.53  % (780)Time elapsed: 0.127 s
% 0.22/0.53  % (780)------------------------------
% 0.22/0.53  % (780)------------------------------
% 0.22/0.54  % (766)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (766)Refutation not found, incomplete strategy% (766)------------------------------
% 0.22/0.54  % (766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (766)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (766)Memory used [KB]: 6140
% 0.22/0.54  % (766)Time elapsed: 0.133 s
% 0.22/0.54  % (766)------------------------------
% 0.22/0.54  % (766)------------------------------
% 0.22/0.54  % (782)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (783)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (782)Refutation not found, incomplete strategy% (782)------------------------------
% 0.22/0.54  % (782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (782)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (782)Memory used [KB]: 6140
% 0.22/0.54  % (782)Time elapsed: 0.128 s
% 0.22/0.54  % (782)------------------------------
% 0.22/0.54  % (782)------------------------------
% 0.22/0.54  % (784)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (778)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (784)Refutation not found, incomplete strategy% (784)------------------------------
% 0.22/0.54  % (784)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (784)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (784)Memory used [KB]: 6140
% 0.22/0.54  % (784)Time elapsed: 0.129 s
% 0.22/0.54  % (784)------------------------------
% 0.22/0.54  % (784)------------------------------
% 0.22/0.54  % (754)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (755)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.41/0.54  % (779)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.41/0.54  % (769)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.41/0.54  % (769)Refutation not found, incomplete strategy% (769)------------------------------
% 1.41/0.54  % (769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.54  % (769)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  % (769)Memory used [KB]: 1663
% 1.41/0.54  % (769)Time elapsed: 0.116 s
% 1.41/0.54  % (769)------------------------------
% 1.41/0.54  % (769)------------------------------
% 1.41/0.54  % (761)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.41/0.55  % (772)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.41/0.55  % (785)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.41/0.55  % (773)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.41/0.55  % (773)Refutation not found, incomplete strategy% (773)------------------------------
% 1.41/0.55  % (773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (773)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (773)Memory used [KB]: 1663
% 1.41/0.55  % (773)Time elapsed: 0.139 s
% 1.41/0.55  % (773)------------------------------
% 1.41/0.55  % (773)------------------------------
% 1.41/0.55  % (772)Refutation not found, incomplete strategy% (772)------------------------------
% 1.41/0.55  % (772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (772)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (772)Memory used [KB]: 1663
% 1.41/0.55  % (772)Time elapsed: 0.139 s
% 1.41/0.55  % (772)------------------------------
% 1.41/0.55  % (772)------------------------------
% 1.41/0.55  % (785)Refutation not found, incomplete strategy% (785)------------------------------
% 1.41/0.55  % (785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (785)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (785)Memory used [KB]: 10618
% 1.41/0.55  % (785)Time elapsed: 0.137 s
% 1.41/0.55  % (785)------------------------------
% 1.41/0.55  % (785)------------------------------
% 1.41/0.55  % (764)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.41/0.55  % (765)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.41/0.55  % (776)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.41/0.55  % (765)Refutation not found, incomplete strategy% (765)------------------------------
% 1.41/0.55  % (765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (765)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (765)Memory used [KB]: 10618
% 1.41/0.55  % (765)Time elapsed: 0.149 s
% 1.41/0.55  % (765)------------------------------
% 1.41/0.55  % (765)------------------------------
% 1.41/0.55  % (783)Refutation not found, incomplete strategy% (783)------------------------------
% 1.41/0.55  % (783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (783)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (783)Memory used [KB]: 6140
% 1.41/0.55  % (783)Time elapsed: 0.147 s
% 1.41/0.55  % (783)------------------------------
% 1.41/0.55  % (783)------------------------------
% 1.41/0.56  % (767)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.41/0.56  % (767)Refutation not found, incomplete strategy% (767)------------------------------
% 1.41/0.56  % (767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (767)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (767)Memory used [KB]: 10618
% 1.41/0.56  % (767)Time elapsed: 0.149 s
% 1.41/0.56  % (767)------------------------------
% 1.41/0.56  % (767)------------------------------
% 1.62/0.57  % (771)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.62/0.58  % (771)Refutation not found, incomplete strategy% (771)------------------------------
% 1.62/0.58  % (771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.62/0.58  % (771)Termination reason: Refutation not found, incomplete strategy
% 1.62/0.58  
% 1.62/0.58  % (771)Memory used [KB]: 10618
% 1.62/0.58  % (771)Time elapsed: 0.170 s
% 1.62/0.58  % (771)------------------------------
% 1.62/0.58  % (771)------------------------------
% 1.96/0.65  % (762)Refutation not found, incomplete strategy% (762)------------------------------
% 1.96/0.65  % (762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.65  % (762)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.65  
% 1.96/0.65  % (762)Memory used [KB]: 6268
% 1.96/0.65  % (762)Time elapsed: 0.235 s
% 1.96/0.65  % (762)------------------------------
% 1.96/0.65  % (762)------------------------------
% 1.96/0.66  % (755)Refutation not found, incomplete strategy% (755)------------------------------
% 1.96/0.66  % (755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.96/0.66  % (755)Termination reason: Refutation not found, incomplete strategy
% 1.96/0.66  
% 1.96/0.66  % (755)Memory used [KB]: 6140
% 1.96/0.66  % (755)Time elapsed: 0.244 s
% 1.96/0.66  % (755)------------------------------
% 1.96/0.66  % (755)------------------------------
% 1.96/0.66  % (790)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.15/0.67  % (791)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.15/0.67  % (754)Refutation not found, incomplete strategy% (754)------------------------------
% 2.15/0.67  % (754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.67  % (754)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.67  
% 2.15/0.67  % (754)Memory used [KB]: 6140
% 2.15/0.67  % (754)Time elapsed: 0.256 s
% 2.15/0.67  % (754)------------------------------
% 2.15/0.67  % (754)------------------------------
% 2.15/0.67  % (792)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.15/0.67  % (788)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.15/0.67  % (792)Refutation not found, incomplete strategy% (792)------------------------------
% 2.15/0.67  % (792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.67  % (792)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.67  
% 2.15/0.67  % (792)Memory used [KB]: 10618
% 2.15/0.67  % (792)Time elapsed: 0.112 s
% 2.15/0.67  % (792)------------------------------
% 2.15/0.67  % (792)------------------------------
% 2.15/0.67  % (796)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.15/0.67  % (795)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.15/0.67  % (795)Refutation not found, incomplete strategy% (795)------------------------------
% 2.15/0.67  % (795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.67  % (795)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.67  
% 2.15/0.67  % (795)Memory used [KB]: 10618
% 2.15/0.67  % (795)Time elapsed: 0.102 s
% 2.15/0.67  % (795)------------------------------
% 2.15/0.67  % (795)------------------------------
% 2.15/0.67  % (794)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.15/0.68  % (793)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.15/0.68  % (794)Refutation not found, incomplete strategy% (794)------------------------------
% 2.15/0.68  % (794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.68  % (794)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.68  
% 2.15/0.68  % (794)Memory used [KB]: 1663
% 2.15/0.68  % (794)Time elapsed: 0.108 s
% 2.15/0.68  % (794)------------------------------
% 2.15/0.68  % (794)------------------------------
% 2.15/0.68  % (793)Refutation not found, incomplete strategy% (793)------------------------------
% 2.15/0.68  % (793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.68  % (793)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.68  
% 2.15/0.68  % (793)Memory used [KB]: 10618
% 2.15/0.68  % (793)Time elapsed: 0.110 s
% 2.15/0.68  % (793)------------------------------
% 2.15/0.68  % (793)------------------------------
% 2.15/0.68  % (798)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.15/0.68  % (798)Refutation not found, incomplete strategy% (798)------------------------------
% 2.15/0.68  % (798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.68  % (798)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.68  
% 2.15/0.68  % (798)Memory used [KB]: 10618
% 2.15/0.68  % (798)Time elapsed: 0.100 s
% 2.15/0.68  % (798)------------------------------
% 2.15/0.68  % (798)------------------------------
% 2.15/0.68  % (797)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.15/0.68  % (770)Refutation not found, incomplete strategy% (770)------------------------------
% 2.15/0.68  % (770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.68  % (770)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.68  
% 2.15/0.68  % (770)Memory used [KB]: 6140
% 2.15/0.68  % (770)Time elapsed: 0.260 s
% 2.15/0.68  % (770)------------------------------
% 2.15/0.68  % (770)------------------------------
% 2.15/0.69  % (800)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.15/0.69  % (800)Refutation not found, incomplete strategy% (800)------------------------------
% 2.15/0.69  % (800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.69  % (800)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.69  
% 2.15/0.69  % (800)Memory used [KB]: 10618
% 2.15/0.69  % (800)Time elapsed: 0.109 s
% 2.15/0.69  % (800)------------------------------
% 2.15/0.69  % (800)------------------------------
% 2.15/0.69  % (799)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.15/0.70  % (801)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.15/0.71  % (802)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.15/0.71  % (802)Refutation not found, incomplete strategy% (802)------------------------------
% 2.15/0.71  % (802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.71  % (802)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.71  
% 2.15/0.71  % (802)Memory used [KB]: 10618
% 2.15/0.71  % (802)Time elapsed: 0.118 s
% 2.15/0.71  % (802)------------------------------
% 2.15/0.71  % (802)------------------------------
% 2.82/0.79  % (803)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.82/0.79  % (804)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.82/0.79  % (805)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 2.82/0.81  % (808)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 2.82/0.81  % (808)Refutation not found, incomplete strategy% (808)------------------------------
% 2.82/0.81  % (808)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.82/0.81  % (808)Termination reason: Refutation not found, incomplete strategy
% 2.82/0.81  
% 2.82/0.81  % (808)Memory used [KB]: 1663
% 2.82/0.81  % (808)Time elapsed: 0.120 s
% 2.82/0.81  % (808)------------------------------
% 2.82/0.81  % (808)------------------------------
% 2.82/0.81  % (807)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 2.82/0.81  % (797)Refutation not found, incomplete strategy% (797)------------------------------
% 2.82/0.81  % (797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.82/0.81  % (797)Termination reason: Refutation not found, incomplete strategy
% 2.82/0.81  
% 2.82/0.81  % (797)Memory used [KB]: 6268
% 2.82/0.81  % (797)Time elapsed: 0.225 s
% 2.82/0.81  % (797)------------------------------
% 2.82/0.81  % (797)------------------------------
% 2.82/0.82  % (809)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 2.82/0.83  % (806)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 3.40/0.88  % (803)Refutation not found, incomplete strategy% (803)------------------------------
% 3.40/0.88  % (803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.40/0.89  % (804)Refutation not found, incomplete strategy% (804)------------------------------
% 3.40/0.89  % (804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.40/0.89  % (803)Termination reason: Refutation not found, incomplete strategy
% 3.40/0.89  
% 3.40/0.89  % (803)Memory used [KB]: 6140
% 3.40/0.89  % (803)Time elapsed: 0.203 s
% 3.40/0.89  % (803)------------------------------
% 3.40/0.89  % (803)------------------------------
% 3.40/0.90  % (804)Termination reason: Refutation not found, incomplete strategy
% 3.40/0.90  
% 3.40/0.90  % (804)Memory used [KB]: 6140
% 3.40/0.90  % (804)Time elapsed: 0.175 s
% 3.40/0.90  % (804)------------------------------
% 3.40/0.90  % (804)------------------------------
% 3.88/0.94  % (758)Time limit reached!
% 3.88/0.94  % (758)------------------------------
% 3.88/0.94  % (758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.88/0.95  % (758)Termination reason: Time limit
% 3.88/0.95  
% 3.88/0.95  % (758)Memory used [KB]: 16375
% 3.88/0.95  % (758)Time elapsed: 0.507 s
% 3.88/0.95  % (758)------------------------------
% 3.88/0.95  % (758)------------------------------
% 4.08/1.00  % (761)Time limit reached!
% 4.08/1.00  % (761)------------------------------
% 4.08/1.00  % (761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.08/1.01  % (761)Termination reason: Time limit
% 4.08/1.01  % (761)Termination phase: Saturation
% 4.08/1.01  
% 4.08/1.01  % (761)Memory used [KB]: 9338
% 4.08/1.01  % (761)Time elapsed: 0.600 s
% 4.08/1.01  % (761)------------------------------
% 4.08/1.01  % (761)------------------------------
% 5.64/1.11  % (806)Time limit reached!
% 5.64/1.11  % (806)------------------------------
% 5.64/1.11  % (806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.64/1.11  % (806)Termination reason: Time limit
% 5.64/1.11  
% 5.64/1.11  % (806)Memory used [KB]: 10106
% 5.64/1.11  % (806)Time elapsed: 0.417 s
% 5.64/1.11  % (806)------------------------------
% 5.64/1.11  % (806)------------------------------
% 5.64/1.11  % (809)Time limit reached!
% 5.64/1.11  % (809)------------------------------
% 5.64/1.11  % (809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.64/1.11  % (809)Termination reason: Time limit
% 5.64/1.11  % (809)Termination phase: Saturation
% 5.64/1.11  
% 5.64/1.11  % (809)Memory used [KB]: 9978
% 5.64/1.11  % (809)Time elapsed: 0.400 s
% 5.64/1.11  % (809)------------------------------
% 5.64/1.11  % (809)------------------------------
% 6.48/1.20  % (805)Time limit reached!
% 6.48/1.20  % (805)------------------------------
% 6.48/1.20  % (805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.48/1.20  % (805)Termination reason: Time limit
% 6.48/1.20  
% 6.48/1.20  % (805)Memory used [KB]: 12792
% 6.48/1.20  % (805)Time elapsed: 0.515 s
% 6.48/1.20  % (805)------------------------------
% 6.48/1.20  % (805)------------------------------
% 7.99/1.37  % (791)Time limit reached!
% 7.99/1.37  % (791)------------------------------
% 7.99/1.37  % (791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.99/1.37  % (791)Termination reason: Time limit
% 7.99/1.37  % (791)Termination phase: Saturation
% 7.99/1.37  
% 7.99/1.37  % (791)Memory used [KB]: 16886
% 7.99/1.37  % (791)Time elapsed: 0.800 s
% 7.99/1.37  % (791)------------------------------
% 7.99/1.37  % (791)------------------------------
% 7.99/1.42  % (801)Refutation found. Thanks to Tanya!
% 7.99/1.42  % SZS status Theorem for theBenchmark
% 7.99/1.42  % SZS output start Proof for theBenchmark
% 7.99/1.42  fof(f12137,plain,(
% 7.99/1.42    $false),
% 7.99/1.42    inference(trivial_inequality_removal,[],[f12136])).
% 7.99/1.42  fof(f12136,plain,(
% 7.99/1.42    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.99/1.42    inference(superposition,[],[f121,f11684])).
% 7.99/1.42  fof(f11684,plain,(
% 7.99/1.42    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 7.99/1.42    inference(forward_demodulation,[],[f11661,f134])).
% 7.99/1.42  fof(f134,plain,(
% 7.99/1.42    ( ! [X2,X1] : (k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X1,X2))) )),
% 7.99/1.42    inference(resolution,[],[f94,f51])).
% 7.99/1.42  fof(f51,plain,(
% 7.99/1.42    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 7.99/1.42    inference(cnf_transformation,[],[f3])).
% 7.99/1.42  fof(f3,axiom,(
% 7.99/1.42    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 7.99/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 7.99/1.42  fof(f94,plain,(
% 7.99/1.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 7.99/1.42    inference(forward_demodulation,[],[f93,f78])).
% 7.99/1.42  fof(f78,plain,(
% 7.99/1.42    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 7.99/1.42    inference(resolution,[],[f55,f56])).
% 7.99/1.42  fof(f56,plain,(
% 7.99/1.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 7.99/1.42    inference(cnf_transformation,[],[f9])).
% 7.99/1.42  fof(f9,axiom,(
% 7.99/1.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 7.99/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 7.99/1.42  fof(f55,plain,(
% 7.99/1.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 7.99/1.42    inference(cnf_transformation,[],[f33])).
% 7.99/1.42  fof(f33,plain,(
% 7.99/1.42    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 7.99/1.42    inference(ennf_transformation,[],[f18])).
% 7.99/1.42  fof(f18,axiom,(
% 7.99/1.42    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 7.99/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 7.99/1.42  fof(f93,plain,(
% 7.99/1.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 7.99/1.42    inference(forward_demodulation,[],[f90,f48])).
% 7.99/1.42  fof(f48,plain,(
% 7.99/1.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 7.99/1.42    inference(cnf_transformation,[],[f12])).
% 7.99/1.42  fof(f12,axiom,(
% 7.99/1.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 7.99/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 7.99/1.42  fof(f90,plain,(
% 7.99/1.42    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 7.99/1.42    inference(resolution,[],[f43,f56])).
% 7.99/1.42  fof(f43,plain,(
% 7.99/1.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 7.99/1.42    inference(cnf_transformation,[],[f25])).
% 7.99/1.42  fof(f25,plain,(
% 7.99/1.42    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.99/1.42    inference(flattening,[],[f24])).
% 7.99/1.42  fof(f24,plain,(
% 7.99/1.42    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.99/1.42    inference(ennf_transformation,[],[f15])).
% 7.99/1.42  fof(f15,axiom,(
% 7.99/1.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 7.99/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 7.99/1.42  fof(f11661,plain,(
% 7.99/1.42    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) )),
% 7.99/1.42    inference(superposition,[],[f1421,f1581])).
% 7.99/1.42  fof(f1581,plain,(
% 7.99/1.42    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),k3_xboole_0(X1,X0))) )),
% 7.99/1.42    inference(forward_demodulation,[],[f1569,f84])).
% 7.99/1.42  fof(f84,plain,(
% 7.99/1.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 7.99/1.42    inference(forward_demodulation,[],[f81,f47])).
% 7.99/1.42  fof(f47,plain,(
% 7.99/1.42    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 7.99/1.42    inference(cnf_transformation,[],[f12])).
% 7.99/1.42  fof(f81,plain,(
% 7.99/1.42    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) )),
% 7.99/1.42    inference(resolution,[],[f49,f56])).
% 7.99/1.42  fof(f49,plain,(
% 7.99/1.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 7.99/1.42    inference(cnf_transformation,[],[f28])).
% 7.99/1.42  fof(f28,plain,(
% 7.99/1.42    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.99/1.42    inference(ennf_transformation,[],[f17])).
% 7.99/1.42  fof(f17,axiom,(
% 7.99/1.42    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 7.99/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 7.99/1.42  fof(f1569,plain,(
% 7.99/1.42    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k7_relat_1(k7_relat_1(k6_relat_1(X1),X0),k1_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) )),
% 7.99/1.42    inference(superposition,[],[f512,f344])).
% 7.99/1.42  fof(f344,plain,(
% 7.99/1.42    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X1),X0) = k3_xboole_0(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X0))) )),
% 7.99/1.42    inference(forward_demodulation,[],[f337,f47])).
% 7.99/1.42  fof(f337,plain,(
% 7.99/1.42    ( ! [X0,X1] : (k3_xboole_0(k6_relat_1(X0),k7_relat_1(k6_relat_1(X1),X0)) = k1_relat_1(k6_relat_1(k7_relat_1(k6_relat_1(X1),X0)))) )),
% 7.99/1.42    inference(superposition,[],[f84,f138])).
% 7.99/1.42  fof(f138,plain,(
% 7.99/1.42    ( ! [X6,X5] : (k6_relat_1(k7_relat_1(k6_relat_1(X6),X5)) = k7_relat_1(k6_relat_1(k6_relat_1(X5)),k7_relat_1(k6_relat_1(X6),X5))) )),
% 7.99/1.42    inference(forward_demodulation,[],[f136,f78])).
% 7.99/1.42  fof(f136,plain,(
% 7.99/1.42    ( ! [X6,X5] : (k6_relat_1(k5_relat_1(k6_relat_1(X5),k6_relat_1(X6))) = k7_relat_1(k6_relat_1(k6_relat_1(X5)),k5_relat_1(k6_relat_1(X5),k6_relat_1(X6)))) )),
% 7.99/1.42    inference(resolution,[],[f94,f63])).
% 7.99/1.42  fof(f63,plain,(
% 7.99/1.42    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0))) )),
% 7.99/1.42    inference(resolution,[],[f53,f56])).
% 7.99/1.42  fof(f53,plain,(
% 7.99/1.42    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) )),
% 7.99/1.42    inference(cnf_transformation,[],[f32])).
% 7.99/1.42  fof(f32,plain,(
% 7.99/1.42    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 7.99/1.42    inference(ennf_transformation,[],[f13])).
% 7.99/1.42  fof(f13,axiom,(
% 7.99/1.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 7.99/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 7.99/1.42  fof(f512,plain,(
% 7.99/1.42    ( ! [X0,X1] : (k3_xboole_0(k6_relat_1(X0),X1) = k7_relat_1(k3_xboole_0(k6_relat_1(X0),X1),k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)))) )),
% 7.99/1.42    inference(resolution,[],[f197,f57])).
% 7.99/1.42  fof(f57,plain,(
% 7.99/1.42    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 7.99/1.42    inference(equality_resolution,[],[f40])).
% 7.99/1.42  fof(f40,plain,(
% 7.99/1.42    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 7.99/1.42    inference(cnf_transformation,[],[f37])).
% 7.99/1.42  fof(f37,plain,(
% 7.99/1.42    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.99/1.42    inference(flattening,[],[f36])).
% 7.99/1.42  fof(f36,plain,(
% 7.99/1.42    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 7.99/1.42    inference(nnf_transformation,[],[f2])).
% 7.99/1.42  fof(f2,axiom,(
% 7.99/1.42    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 7.99/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 7.99/1.42  fof(f197,plain,(
% 7.99/1.42    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)),X2) | k3_xboole_0(k6_relat_1(X0),X1) = k7_relat_1(k3_xboole_0(k6_relat_1(X0),X1),X2)) )),
% 7.99/1.42    inference(forward_demodulation,[],[f193,f162])).
% 7.99/1.42  fof(f162,plain,(
% 7.99/1.42    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k3_xboole_0(k6_relat_1(X1),X2)) = k7_relat_1(k3_xboole_0(k6_relat_1(X1),X2),X0)) )),
% 7.99/1.42    inference(resolution,[],[f79,f56])).
% 7.99/1.42  fof(f79,plain,(
% 7.99/1.42    ( ! [X4,X2,X3] : (~v1_relat_1(X3) | k5_relat_1(k6_relat_1(X2),k3_xboole_0(X3,X4)) = k7_relat_1(k3_xboole_0(X3,X4),X2)) )),
% 7.99/1.42    inference(resolution,[],[f55,f50])).
% 7.99/1.42  fof(f50,plain,(
% 7.99/1.42    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 7.99/1.42    inference(cnf_transformation,[],[f29])).
% 7.99/1.42  fof(f29,plain,(
% 7.99/1.42    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 7.99/1.42    inference(ennf_transformation,[],[f10])).
% 7.99/1.42  fof(f10,axiom,(
% 7.99/1.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 7.99/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 7.99/1.42  fof(f193,plain,(
% 7.99/1.42    ( ! [X2,X0,X1] : (k3_xboole_0(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X2),k3_xboole_0(k6_relat_1(X0),X1)) | ~r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)),X2)) )),
% 7.99/1.42    inference(resolution,[],[f86,f56])).
% 7.99/1.42  fof(f86,plain,(
% 7.99/1.42    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k3_xboole_0(X2,X3) = k5_relat_1(k6_relat_1(X4),k3_xboole_0(X2,X3)) | ~r1_tarski(k1_relat_1(k3_xboole_0(X2,X3)),X4)) )),
% 7.99/1.42    inference(resolution,[],[f42,f50])).
% 7.99/1.42  fof(f42,plain,(
% 7.99/1.42    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 7.99/1.42    inference(cnf_transformation,[],[f23])).
% 7.99/1.42  fof(f23,plain,(
% 7.99/1.42    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 7.99/1.42    inference(flattening,[],[f22])).
% 7.99/1.42  fof(f22,plain,(
% 7.99/1.42    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 7.99/1.42    inference(ennf_transformation,[],[f14])).
% 7.99/1.42  fof(f14,axiom,(
% 7.99/1.42    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 7.99/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 7.99/1.42  fof(f1421,plain,(
% 7.99/1.42    ( ! [X12,X13,X11] : (k7_relat_1(k7_relat_1(k6_relat_1(X13),X11),k3_xboole_0(X12,X11)) = k7_relat_1(k6_relat_1(X13),k3_xboole_0(X12,X11))) )),
% 7.99/1.42    inference(forward_demodulation,[],[f1406,f78])).
% 7.99/1.42  fof(f1406,plain,(
% 7.99/1.42    ( ! [X12,X13,X11] : (k7_relat_1(k7_relat_1(k6_relat_1(X13),X11),k3_xboole_0(X12,X11)) = k5_relat_1(k6_relat_1(k3_xboole_0(X12,X11)),k6_relat_1(X13))) )),
% 7.99/1.42    inference(superposition,[],[f425,f135])).
% 7.99/1.42  fof(f135,plain,(
% 7.99/1.42    ( ! [X4,X3] : (k6_relat_1(k3_xboole_0(X3,X4)) = k7_relat_1(k6_relat_1(X4),k3_xboole_0(X3,X4))) )),
% 7.99/1.42    inference(resolution,[],[f94,f60])).
% 7.99/1.42  fof(f60,plain,(
% 7.99/1.42    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X3,X2),X2)) )),
% 7.99/1.42    inference(superposition,[],[f51,f44])).
% 7.99/1.42  fof(f44,plain,(
% 7.99/1.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 7.99/1.42    inference(cnf_transformation,[],[f1])).
% 7.99/1.42  fof(f1,axiom,(
% 7.99/1.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 7.99/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 7.99/1.42  fof(f425,plain,(
% 7.99/1.42    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 7.99/1.42    inference(forward_demodulation,[],[f424,f418])).
% 7.99/1.42  fof(f418,plain,(
% 7.99/1.42    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) )),
% 7.99/1.42    inference(forward_demodulation,[],[f414,f78])).
% 7.99/1.42  fof(f414,plain,(
% 7.99/1.42    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X0)) )),
% 7.99/1.42    inference(resolution,[],[f174,f56])).
% 7.99/1.42  fof(f174,plain,(
% 7.99/1.42    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),k5_relat_1(X1,k6_relat_1(X2))) = k7_relat_1(k5_relat_1(X1,k6_relat_1(X2)),X0)) )),
% 7.99/1.42    inference(resolution,[],[f80,f56])).
% 7.99/1.42  fof(f80,plain,(
% 7.99/1.42    ( ! [X6,X7,X5] : (~v1_relat_1(X7) | k5_relat_1(k6_relat_1(X5),k5_relat_1(X6,X7)) = k7_relat_1(k5_relat_1(X6,X7),X5) | ~v1_relat_1(X6)) )),
% 7.99/1.42    inference(resolution,[],[f55,f52])).
% 7.99/1.42  fof(f52,plain,(
% 7.99/1.42    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.99/1.42    inference(cnf_transformation,[],[f31])).
% 7.99/1.42  fof(f31,plain,(
% 7.99/1.42    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 7.99/1.42    inference(flattening,[],[f30])).
% 7.99/1.42  fof(f30,plain,(
% 7.99/1.42    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 7.99/1.42    inference(ennf_transformation,[],[f8])).
% 7.99/1.42  fof(f8,axiom,(
% 7.99/1.42    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 7.99/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 7.99/1.42  fof(f424,plain,(
% 7.99/1.42    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 7.99/1.42    inference(forward_demodulation,[],[f420,f78])).
% 7.99/1.42  fof(f420,plain,(
% 7.99/1.42    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2))) )),
% 7.99/1.42    inference(resolution,[],[f192,f56])).
% 7.99/1.42  fof(f192,plain,(
% 7.99/1.42    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1))) )),
% 7.99/1.42    inference(forward_demodulation,[],[f188,f78])).
% 7.99/1.42  fof(f188,plain,(
% 7.99/1.42    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 7.99/1.42    inference(resolution,[],[f95,f56])).
% 7.99/1.42  fof(f95,plain,(
% 7.99/1.42    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 7.99/1.42    inference(resolution,[],[f45,f56])).
% 7.99/1.42  fof(f45,plain,(
% 7.99/1.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 7.99/1.42    inference(cnf_transformation,[],[f26])).
% 7.99/1.42  fof(f26,plain,(
% 7.99/1.42    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 7.99/1.42    inference(ennf_transformation,[],[f11])).
% 7.99/1.42  fof(f11,axiom,(
% 7.99/1.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 7.99/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 7.99/1.42  fof(f121,plain,(
% 7.99/1.42    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 7.99/1.42    inference(superposition,[],[f38,f78])).
% 7.99/1.42  fof(f38,plain,(
% 7.99/1.42    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.99/1.42    inference(cnf_transformation,[],[f35])).
% 7.99/1.42  fof(f35,plain,(
% 7.99/1.42    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.99/1.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f34])).
% 7.99/1.42  fof(f34,plain,(
% 7.99/1.42    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 7.99/1.42    introduced(choice_axiom,[])).
% 7.99/1.42  fof(f21,plain,(
% 7.99/1.42    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 7.99/1.42    inference(ennf_transformation,[],[f20])).
% 7.99/1.42  fof(f20,negated_conjecture,(
% 7.99/1.42    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 7.99/1.42    inference(negated_conjecture,[],[f19])).
% 7.99/1.42  fof(f19,conjecture,(
% 7.99/1.42    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 7.99/1.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 7.99/1.42  % SZS output end Proof for theBenchmark
% 7.99/1.42  % (801)------------------------------
% 7.99/1.42  % (801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.99/1.42  % (801)Termination reason: Refutation
% 7.99/1.42  
% 7.99/1.42  % (801)Memory used [KB]: 14711
% 7.99/1.42  % (801)Time elapsed: 0.845 s
% 7.99/1.42  % (801)------------------------------
% 7.99/1.42  % (801)------------------------------
% 7.99/1.42  % (751)Success in time 1.071 s
%------------------------------------------------------------------------------

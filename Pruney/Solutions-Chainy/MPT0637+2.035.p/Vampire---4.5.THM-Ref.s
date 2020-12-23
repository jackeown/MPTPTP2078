%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:27 EST 2020

% Result     : Theorem 3.59s
% Output     : Refutation 3.59s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 303 expanded)
%              Number of leaves         :   15 (  86 expanded)
%              Depth                    :   17
%              Number of atoms          :  150 ( 492 expanded)
%              Number of equality atoms :   73 ( 214 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5168,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f5166])).

fof(f5166,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f37,f4279])).

fof(f4279,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f78,f4278])).

fof(f4278,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k6_relat_1(k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f4277,f127])).

fof(f127,plain,(
    ! [X2,X1] : k6_relat_1(k3_xboole_0(X1,X2)) = k8_relat_1(X1,k6_relat_1(k3_xboole_0(X1,X2))) ),
    inference(resolution,[],[f96,f43])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f94,f40])).

fof(f40,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(resolution,[],[f54,f38])).

fof(f38,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f4277,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k6_relat_1(k3_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f4225,f128])).

fof(f128,plain,(
    ! [X4,X3] : k6_relat_1(k3_xboole_0(X3,X4)) = k8_relat_1(X4,k6_relat_1(k3_xboole_0(X3,X4))) ),
    inference(resolution,[],[f96,f63])).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f43,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f4225,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(k3_xboole_0(X2,X3)))) ),
    inference(superposition,[],[f1203,f746])).

fof(f746,plain,(
    ! [X14,X15,X13] : k7_relat_1(k8_relat_1(X13,k6_relat_1(X14)),X15) = k8_relat_1(X13,k8_relat_1(X14,k6_relat_1(X15))) ),
    inference(forward_demodulation,[],[f721,f745])).

fof(f745,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k8_relat_1(X2,k6_relat_1(X1))) = k8_relat_1(X2,k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(backward_demodulation,[],[f357,f719])).

fof(f719,plain,(
    ! [X8,X7,X9] : k8_relat_1(X9,k8_relat_1(X7,k6_relat_1(X8))) = k5_relat_1(k8_relat_1(X7,k6_relat_1(X8)),k6_relat_1(X9)) ),
    inference(superposition,[],[f79,f271])).

fof(f271,plain,(
    ! [X4,X5] : k8_relat_1(X4,k6_relat_1(X5)) = k3_xboole_0(k6_relat_1(X4),k8_relat_1(X4,k6_relat_1(X5))) ),
    inference(forward_demodulation,[],[f268,f39])).

fof(f39,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f268,plain,(
    ! [X4,X5] : k3_xboole_0(k6_relat_1(X4),k8_relat_1(X4,k6_relat_1(X5))) = k1_relat_1(k6_relat_1(k8_relat_1(X4,k6_relat_1(X5)))) ),
    inference(superposition,[],[f93,f129])).

fof(f129,plain,(
    ! [X6,X5] : k6_relat_1(k8_relat_1(X5,k6_relat_1(X6))) = k8_relat_1(k6_relat_1(X5),k6_relat_1(k8_relat_1(X5,k6_relat_1(X6)))) ),
    inference(resolution,[],[f96,f80])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f70,f78])).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X1)) ),
    inference(resolution,[],[f53,f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f93,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f92,f85])).

fof(f85,plain,(
    ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f83,f78])).

fof(f83,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f50,f38])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f92,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f90,f39])).

fof(f90,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) ),
    inference(resolution,[],[f51,f38])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f79,plain,(
    ! [X4,X2,X3] : k8_relat_1(X2,k3_xboole_0(k6_relat_1(X3),X4)) = k5_relat_1(k3_xboole_0(k6_relat_1(X3),X4),k6_relat_1(X2)) ),
    inference(resolution,[],[f49,f62])).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f48,f38])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f357,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k8_relat_1(X2,k6_relat_1(X1))) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f352,f78])).

fof(f352,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k8_relat_1(X2,k6_relat_1(X1))) ),
    inference(resolution,[],[f142,f38])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k8_relat_1(X2,k6_relat_1(X1))) ) ),
    inference(forward_demodulation,[],[f139,f78])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f102,f38])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f42,f38])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f721,plain,(
    ! [X14,X15,X13] : k5_relat_1(k6_relat_1(X15),k8_relat_1(X13,k6_relat_1(X14))) = k7_relat_1(k8_relat_1(X13,k6_relat_1(X14)),X15) ),
    inference(superposition,[],[f84,f271])).

fof(f84,plain,(
    ! [X4,X2,X3] : k5_relat_1(k6_relat_1(X2),k3_xboole_0(k6_relat_1(X3),X4)) = k7_relat_1(k3_xboole_0(k6_relat_1(X3),X4),X2) ),
    inference(resolution,[],[f50,f62])).

fof(f1203,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f1191,f93])).

fof(f1191,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[],[f367,f271])).

fof(f367,plain,(
    ! [X0,X1] : k3_xboole_0(k6_relat_1(X0),X1) = k7_relat_1(k3_xboole_0(k6_relat_1(X0),X1),k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1))) ),
    inference(resolution,[],[f101,f60])).

fof(f60,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
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

fof(f101,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X2),X3)),X4)
      | k3_xboole_0(k6_relat_1(X2),X3) = k7_relat_1(k3_xboole_0(k6_relat_1(X2),X3),X4) ) ),
    inference(forward_demodulation,[],[f98,f84])).

fof(f98,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X2),X3)),X4)
      | k3_xboole_0(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X4),k3_xboole_0(k6_relat_1(X2),X3)) ) ),
    inference(resolution,[],[f55,f62])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f78,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f49,f38])).

fof(f37,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f33])).

fof(f33,plain,
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
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:28:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (18517)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (18533)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (18525)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (18514)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (18513)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (18513)Refutation not found, incomplete strategy% (18513)------------------------------
% 0.21/0.54  % (18513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (18513)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (18513)Memory used [KB]: 1663
% 0.21/0.54  % (18513)Time elapsed: 0.119 s
% 0.21/0.54  % (18513)------------------------------
% 0.21/0.54  % (18513)------------------------------
% 0.21/0.55  % (18524)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.55  % (18524)Refutation not found, incomplete strategy% (18524)------------------------------
% 0.21/0.55  % (18524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18515)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (18516)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.55  % (18524)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (18524)Memory used [KB]: 10618
% 0.21/0.55  % (18524)Time elapsed: 0.123 s
% 0.21/0.55  % (18524)------------------------------
% 0.21/0.55  % (18524)------------------------------
% 0.21/0.55  % (18523)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (18541)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (18512)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (18535)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (18523)Refutation not found, incomplete strategy% (18523)------------------------------
% 0.21/0.55  % (18523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (18538)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (18540)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (18520)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (18522)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (18539)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (18523)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18523)Memory used [KB]: 6140
% 0.21/0.56  % (18523)Time elapsed: 0.121 s
% 0.21/0.56  % (18523)------------------------------
% 0.21/0.56  % (18523)------------------------------
% 0.21/0.56  % (18527)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.56  % (18530)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (18538)Refutation not found, incomplete strategy% (18538)------------------------------
% 0.21/0.56  % (18538)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18531)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.56  % (18530)Refutation not found, incomplete strategy% (18530)------------------------------
% 0.21/0.56  % (18530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18532)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.56  % (18522)Refutation not found, incomplete strategy% (18522)------------------------------
% 0.21/0.56  % (18522)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18530)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18530)Memory used [KB]: 1663
% 0.21/0.56  % (18530)Time elapsed: 0.146 s
% 0.21/0.56  % (18530)------------------------------
% 0.21/0.56  % (18530)------------------------------
% 0.21/0.56  % (18540)Refutation not found, incomplete strategy% (18540)------------------------------
% 0.21/0.56  % (18540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (18536)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (18538)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (18538)Memory used [KB]: 6140
% 0.21/0.56  % (18538)Time elapsed: 0.147 s
% 0.21/0.56  % (18538)------------------------------
% 0.21/0.56  % (18538)------------------------------
% 0.21/0.56  % (18528)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.57  % (18519)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.57  % (18522)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  % (18536)Refutation not found, incomplete strategy% (18536)------------------------------
% 0.21/0.57  % (18536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (18536)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (18536)Memory used [KB]: 10618
% 0.21/0.57  % (18536)Time elapsed: 0.144 s
% 0.21/0.57  % (18536)------------------------------
% 0.21/0.57  % (18536)------------------------------
% 0.21/0.57  
% 0.21/0.57  % (18522)Memory used [KB]: 10618
% 0.21/0.57  % (18522)Time elapsed: 0.148 s
% 0.21/0.57  % (18522)------------------------------
% 0.21/0.57  % (18522)------------------------------
% 1.53/0.57  % (18529)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.53/0.57  % (18539)Refutation not found, incomplete strategy% (18539)------------------------------
% 1.53/0.57  % (18539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (18528)Refutation not found, incomplete strategy% (18528)------------------------------
% 1.53/0.57  % (18528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (18528)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (18528)Memory used [KB]: 10618
% 1.53/0.57  % (18528)Time elapsed: 0.145 s
% 1.53/0.57  % (18528)------------------------------
% 1.53/0.57  % (18528)------------------------------
% 1.53/0.57  % (18521)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.53/0.57  % (18541)Refutation not found, incomplete strategy% (18541)------------------------------
% 1.53/0.57  % (18541)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (18541)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (18541)Memory used [KB]: 1663
% 1.53/0.57  % (18541)Time elapsed: 0.003 s
% 1.53/0.57  % (18541)------------------------------
% 1.53/0.57  % (18541)------------------------------
% 1.53/0.57  % (18529)Refutation not found, incomplete strategy% (18529)------------------------------
% 1.53/0.57  % (18529)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (18529)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (18529)Memory used [KB]: 1663
% 1.53/0.57  % (18529)Time elapsed: 0.150 s
% 1.53/0.57  % (18529)------------------------------
% 1.53/0.57  % (18529)------------------------------
% 1.53/0.58  % (18540)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (18540)Memory used [KB]: 10618
% 1.53/0.58  % (18540)Time elapsed: 0.149 s
% 1.53/0.58  % (18540)------------------------------
% 1.53/0.58  % (18540)------------------------------
% 1.53/0.58  % (18537)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.53/0.58  % (18537)Refutation not found, incomplete strategy% (18537)------------------------------
% 1.53/0.58  % (18537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.58  % (18539)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.58  
% 1.53/0.58  % (18539)Memory used [KB]: 6140
% 1.53/0.58  % (18539)Time elapsed: 0.147 s
% 1.53/0.58  % (18539)------------------------------
% 1.53/0.58  % (18539)------------------------------
% 1.53/0.58  % (18518)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.77/0.59  % (18537)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.59  
% 1.77/0.59  % (18537)Memory used [KB]: 6140
% 1.77/0.59  % (18537)Time elapsed: 0.156 s
% 1.77/0.59  % (18537)------------------------------
% 1.77/0.59  % (18537)------------------------------
% 1.77/0.60  % (18534)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.77/0.60  % (18526)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.77/0.60  % (18526)Refutation not found, incomplete strategy% (18526)------------------------------
% 1.77/0.60  % (18526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.77/0.61  % (18526)Termination reason: Refutation not found, incomplete strategy
% 1.77/0.61  
% 1.77/0.61  % (18526)Memory used [KB]: 1663
% 1.77/0.61  % (18526)Time elapsed: 0.151 s
% 1.77/0.61  % (18526)------------------------------
% 1.77/0.61  % (18526)------------------------------
% 2.36/0.71  % (18514)Refutation not found, incomplete strategy% (18514)------------------------------
% 2.36/0.71  % (18514)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.71  % (18514)Termination reason: Refutation not found, incomplete strategy
% 2.36/0.71  
% 2.36/0.71  % (18514)Memory used [KB]: 6140
% 2.36/0.71  % (18514)Time elapsed: 0.292 s
% 2.36/0.71  % (18514)------------------------------
% 2.36/0.71  % (18514)------------------------------
% 2.36/0.72  % (18527)Refutation not found, incomplete strategy% (18527)------------------------------
% 2.36/0.72  % (18527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.72  % (18527)Termination reason: Refutation not found, incomplete strategy
% 2.36/0.72  
% 2.36/0.72  % (18527)Memory used [KB]: 6140
% 2.36/0.72  % (18527)Time elapsed: 0.218 s
% 2.36/0.72  % (18527)------------------------------
% 2.36/0.72  % (18527)------------------------------
% 2.36/0.72  % (18549)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.36/0.72  % (18546)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.36/0.73  % (18552)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.36/0.73  % (18552)Refutation not found, incomplete strategy% (18552)------------------------------
% 2.36/0.73  % (18552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.73  % (18552)Termination reason: Refutation not found, incomplete strategy
% 2.36/0.73  
% 2.36/0.73  % (18552)Memory used [KB]: 10618
% 2.36/0.73  % (18552)Time elapsed: 0.135 s
% 2.36/0.73  % (18552)------------------------------
% 2.36/0.73  % (18552)------------------------------
% 2.36/0.73  % (18551)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.36/0.74  % (18554)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.36/0.74  % (18549)Refutation not found, incomplete strategy% (18549)------------------------------
% 2.36/0.74  % (18549)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.74  % (18549)Termination reason: Refutation not found, incomplete strategy
% 2.36/0.74  
% 2.36/0.74  % (18549)Memory used [KB]: 10618
% 2.36/0.74  % (18549)Time elapsed: 0.133 s
% 2.36/0.74  % (18549)------------------------------
% 2.36/0.74  % (18549)------------------------------
% 2.36/0.74  % (18556)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.36/0.74  % (18556)Refutation not found, incomplete strategy% (18556)------------------------------
% 2.36/0.74  % (18556)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.74  % (18556)Termination reason: Refutation not found, incomplete strategy
% 2.36/0.74  
% 2.36/0.74  % (18556)Memory used [KB]: 10618
% 2.36/0.74  % (18556)Time elapsed: 0.133 s
% 2.36/0.74  % (18556)------------------------------
% 2.36/0.74  % (18556)------------------------------
% 2.36/0.75  % (18566)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.36/0.75  % (18550)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.36/0.75  % (18550)Refutation not found, incomplete strategy% (18550)------------------------------
% 2.36/0.75  % (18550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.75  % (18550)Termination reason: Refutation not found, incomplete strategy
% 2.36/0.75  
% 2.36/0.75  % (18550)Memory used [KB]: 10618
% 2.36/0.75  % (18550)Time elapsed: 0.141 s
% 2.36/0.75  % (18550)------------------------------
% 2.36/0.75  % (18550)------------------------------
% 2.36/0.75  % (18551)Refutation not found, incomplete strategy% (18551)------------------------------
% 2.36/0.75  % (18551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.75  % (18551)Termination reason: Refutation not found, incomplete strategy
% 2.36/0.75  
% 2.36/0.75  % (18551)Memory used [KB]: 1663
% 2.36/0.75  % (18551)Time elapsed: 0.144 s
% 2.36/0.75  % (18551)------------------------------
% 2.36/0.75  % (18551)------------------------------
% 2.36/0.76  % (18515)Refutation not found, incomplete strategy% (18515)------------------------------
% 2.36/0.76  % (18515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.36/0.76  % (18547)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.36/0.76  % (18548)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.86/0.78  % (18553)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.86/0.78  % (18515)Termination reason: Refutation not found, incomplete strategy
% 2.86/0.78  
% 2.86/0.78  % (18515)Memory used [KB]: 6140
% 2.86/0.78  % (18515)Time elapsed: 0.334 s
% 2.86/0.78  % (18515)------------------------------
% 2.86/0.78  % (18515)------------------------------
% 2.86/0.79  % (18520)Refutation not found, incomplete strategy% (18520)------------------------------
% 2.86/0.79  % (18520)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.86/0.79  % (18520)Termination reason: Refutation not found, incomplete strategy
% 2.86/0.79  
% 2.86/0.79  % (18520)Memory used [KB]: 6268
% 2.86/0.79  % (18520)Time elapsed: 0.379 s
% 2.86/0.79  % (18520)------------------------------
% 2.86/0.79  % (18520)------------------------------
% 2.86/0.80  % (18562)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.86/0.80  % (18562)Refutation not found, incomplete strategy% (18562)------------------------------
% 2.86/0.80  % (18562)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.86/0.80  % (18562)Termination reason: Refutation not found, incomplete strategy
% 2.86/0.80  
% 2.86/0.80  % (18562)Memory used [KB]: 10618
% 2.86/0.80  % (18562)Time elapsed: 0.170 s
% 2.86/0.80  % (18562)------------------------------
% 2.86/0.80  % (18562)------------------------------
% 2.86/0.80  % (18558)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.86/0.83  % (18577)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.86/0.83  % (18577)Refutation not found, incomplete strategy% (18577)------------------------------
% 2.86/0.83  % (18577)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.86/0.83  % (18577)Termination reason: Refutation not found, incomplete strategy
% 2.86/0.83  
% 2.86/0.83  % (18577)Memory used [KB]: 10618
% 2.86/0.83  % (18577)Time elapsed: 0.182 s
% 2.86/0.83  % (18577)------------------------------
% 2.86/0.83  % (18577)------------------------------
% 2.86/0.85  % (18589)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.86/0.85  % (18590)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.41/0.86  % (18588)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.41/0.87  % (18591)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 3.41/0.87  % (18554)Refutation not found, incomplete strategy% (18554)------------------------------
% 3.41/0.87  % (18554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.41/0.87  % (18554)Termination reason: Refutation not found, incomplete strategy
% 3.41/0.87  
% 3.41/0.87  % (18554)Memory used [KB]: 6268
% 3.41/0.87  % (18554)Time elapsed: 0.275 s
% 3.41/0.87  % (18554)------------------------------
% 3.41/0.87  % (18554)------------------------------
% 3.59/0.89  % (18594)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 3.59/0.89  % (18595)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.59/0.89  % (18594)Refutation not found, incomplete strategy% (18594)------------------------------
% 3.59/0.89  % (18594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.59/0.89  % (18594)Termination reason: Refutation not found, incomplete strategy
% 3.59/0.89  
% 3.59/0.89  % (18594)Memory used [KB]: 1663
% 3.59/0.89  % (18594)Time elapsed: 0.095 s
% 3.59/0.89  % (18594)------------------------------
% 3.59/0.89  % (18594)------------------------------
% 3.59/0.89  % (18593)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 3.59/0.92  % (18519)Refutation found. Thanks to Tanya!
% 3.59/0.92  % SZS status Theorem for theBenchmark
% 3.59/0.92  % SZS output start Proof for theBenchmark
% 3.59/0.92  fof(f5168,plain,(
% 3.59/0.92    $false),
% 3.59/0.92    inference(trivial_inequality_removal,[],[f5166])).
% 3.59/0.92  fof(f5166,plain,(
% 3.59/0.92    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.59/0.92    inference(superposition,[],[f37,f4279])).
% 3.59/0.92  fof(f4279,plain,(
% 3.59/0.92    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 3.59/0.92    inference(backward_demodulation,[],[f78,f4278])).
% 3.59/0.92  fof(f4278,plain,(
% 3.59/0.92    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k6_relat_1(k3_xboole_0(X2,X3))) )),
% 3.59/0.92    inference(forward_demodulation,[],[f4277,f127])).
% 3.59/0.92  fof(f127,plain,(
% 3.59/0.92    ( ! [X2,X1] : (k6_relat_1(k3_xboole_0(X1,X2)) = k8_relat_1(X1,k6_relat_1(k3_xboole_0(X1,X2)))) )),
% 3.59/0.92    inference(resolution,[],[f96,f43])).
% 3.59/0.92  fof(f43,plain,(
% 3.59/0.92    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.59/0.92    inference(cnf_transformation,[],[f3])).
% 3.59/0.92  fof(f3,axiom,(
% 3.59/0.92    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.59/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.59/0.92  fof(f96,plain,(
% 3.59/0.92    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 3.59/0.92    inference(forward_demodulation,[],[f94,f40])).
% 3.59/0.92  fof(f40,plain,(
% 3.59/0.92    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.59/0.92    inference(cnf_transformation,[],[f13])).
% 3.59/0.92  fof(f13,axiom,(
% 3.59/0.92    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.59/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 3.59/0.92  fof(f94,plain,(
% 3.59/0.92    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 3.59/0.92    inference(resolution,[],[f54,f38])).
% 3.59/0.92  fof(f38,plain,(
% 3.59/0.92    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.59/0.92    inference(cnf_transformation,[],[f8])).
% 3.59/0.92  fof(f8,axiom,(
% 3.59/0.92    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.59/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 3.59/0.92  fof(f54,plain,(
% 3.59/0.92    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 3.59/0.92    inference(cnf_transformation,[],[f30])).
% 3.59/0.92  fof(f30,plain,(
% 3.59/0.92    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.59/0.92    inference(flattening,[],[f29])).
% 3.59/0.92  fof(f29,plain,(
% 3.59/0.92    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.59/0.92    inference(ennf_transformation,[],[f11])).
% 3.59/0.92  fof(f11,axiom,(
% 3.59/0.92    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 3.59/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 3.59/0.92  fof(f4277,plain,(
% 3.59/0.92    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k6_relat_1(k3_xboole_0(X2,X3)))) )),
% 3.59/0.92    inference(forward_demodulation,[],[f4225,f128])).
% 3.59/0.92  fof(f128,plain,(
% 3.59/0.92    ( ! [X4,X3] : (k6_relat_1(k3_xboole_0(X3,X4)) = k8_relat_1(X4,k6_relat_1(k3_xboole_0(X3,X4)))) )),
% 3.59/0.92    inference(resolution,[],[f96,f63])).
% 3.59/0.92  fof(f63,plain,(
% 3.59/0.92    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 3.59/0.92    inference(superposition,[],[f43,f44])).
% 3.59/0.92  fof(f44,plain,(
% 3.59/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.59/0.92    inference(cnf_transformation,[],[f1])).
% 3.59/0.92  fof(f1,axiom,(
% 3.59/0.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.59/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.59/0.92  fof(f4225,plain,(
% 3.59/0.92    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(k3_xboole_0(X2,X3))))) )),
% 3.59/0.92    inference(superposition,[],[f1203,f746])).
% 3.59/0.92  fof(f746,plain,(
% 3.59/0.92    ( ! [X14,X15,X13] : (k7_relat_1(k8_relat_1(X13,k6_relat_1(X14)),X15) = k8_relat_1(X13,k8_relat_1(X14,k6_relat_1(X15)))) )),
% 3.59/0.92    inference(forward_demodulation,[],[f721,f745])).
% 3.59/0.92  fof(f745,plain,(
% 3.59/0.92    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k8_relat_1(X2,k6_relat_1(X1))) = k8_relat_1(X2,k8_relat_1(X1,k6_relat_1(X0)))) )),
% 3.59/0.92    inference(backward_demodulation,[],[f357,f719])).
% 3.59/0.92  fof(f719,plain,(
% 3.59/0.92    ( ! [X8,X7,X9] : (k8_relat_1(X9,k8_relat_1(X7,k6_relat_1(X8))) = k5_relat_1(k8_relat_1(X7,k6_relat_1(X8)),k6_relat_1(X9))) )),
% 3.59/0.92    inference(superposition,[],[f79,f271])).
% 3.59/0.92  fof(f271,plain,(
% 3.59/0.92    ( ! [X4,X5] : (k8_relat_1(X4,k6_relat_1(X5)) = k3_xboole_0(k6_relat_1(X4),k8_relat_1(X4,k6_relat_1(X5)))) )),
% 3.59/0.92    inference(forward_demodulation,[],[f268,f39])).
% 3.59/0.92  fof(f39,plain,(
% 3.59/0.92    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.59/0.92    inference(cnf_transformation,[],[f13])).
% 3.59/0.92  fof(f268,plain,(
% 3.59/0.92    ( ! [X4,X5] : (k3_xboole_0(k6_relat_1(X4),k8_relat_1(X4,k6_relat_1(X5))) = k1_relat_1(k6_relat_1(k8_relat_1(X4,k6_relat_1(X5))))) )),
% 3.59/0.92    inference(superposition,[],[f93,f129])).
% 3.59/0.92  fof(f129,plain,(
% 3.59/0.92    ( ! [X6,X5] : (k6_relat_1(k8_relat_1(X5,k6_relat_1(X6))) = k8_relat_1(k6_relat_1(X5),k6_relat_1(k8_relat_1(X5,k6_relat_1(X6))))) )),
% 3.59/0.92    inference(resolution,[],[f96,f80])).
% 3.59/0.92  fof(f80,plain,(
% 3.59/0.92    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X1))) )),
% 3.59/0.92    inference(backward_demodulation,[],[f70,f78])).
% 3.59/0.92  fof(f70,plain,(
% 3.59/0.92    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X1))) )),
% 3.59/0.92    inference(resolution,[],[f53,f38])).
% 3.59/0.92  fof(f53,plain,(
% 3.59/0.92    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)) )),
% 3.59/0.92    inference(cnf_transformation,[],[f28])).
% 3.59/0.92  fof(f28,plain,(
% 3.59/0.92    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 3.59/0.92    inference(ennf_transformation,[],[f14])).
% 3.59/0.92  fof(f14,axiom,(
% 3.59/0.92    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 3.59/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 3.59/0.92  fof(f93,plain,(
% 3.59/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 3.59/0.92    inference(forward_demodulation,[],[f92,f85])).
% 3.59/0.92  fof(f85,plain,(
% 3.59/0.92    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 3.59/0.92    inference(forward_demodulation,[],[f83,f78])).
% 3.59/0.92  fof(f83,plain,(
% 3.59/0.92    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 3.59/0.92    inference(resolution,[],[f50,f38])).
% 3.59/0.92  fof(f50,plain,(
% 3.59/0.92    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 3.59/0.92    inference(cnf_transformation,[],[f26])).
% 3.59/0.92  fof(f26,plain,(
% 3.59/0.92    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.59/0.92    inference(ennf_transformation,[],[f18])).
% 3.59/0.92  fof(f18,axiom,(
% 3.59/0.92    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.59/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 3.59/0.92  fof(f92,plain,(
% 3.59/0.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 3.59/0.92    inference(forward_demodulation,[],[f90,f39])).
% 3.59/0.92  fof(f90,plain,(
% 3.59/0.92    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) )),
% 3.59/0.92    inference(resolution,[],[f51,f38])).
% 3.59/0.92  fof(f51,plain,(
% 3.59/0.92    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 3.59/0.92    inference(cnf_transformation,[],[f27])).
% 3.59/0.92  fof(f27,plain,(
% 3.59/0.92    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.59/0.92    inference(ennf_transformation,[],[f17])).
% 3.59/0.92  fof(f17,axiom,(
% 3.59/0.92    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 3.59/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 3.59/0.92  fof(f79,plain,(
% 3.59/0.92    ( ! [X4,X2,X3] : (k8_relat_1(X2,k3_xboole_0(k6_relat_1(X3),X4)) = k5_relat_1(k3_xboole_0(k6_relat_1(X3),X4),k6_relat_1(X2))) )),
% 3.59/0.92    inference(resolution,[],[f49,f62])).
% 3.59/0.92  fof(f62,plain,(
% 3.59/0.92    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(k6_relat_1(X0),X1))) )),
% 3.59/0.92    inference(resolution,[],[f48,f38])).
% 3.59/0.92  fof(f48,plain,(
% 3.59/0.92    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1))) )),
% 3.59/0.92    inference(cnf_transformation,[],[f24])).
% 3.59/0.92  fof(f24,plain,(
% 3.59/0.92    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 3.59/0.92    inference(ennf_transformation,[],[f9])).
% 3.59/0.92  fof(f9,axiom,(
% 3.59/0.92    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 3.59/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 3.59/0.92  fof(f49,plain,(
% 3.59/0.92    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 3.59/0.92    inference(cnf_transformation,[],[f25])).
% 3.59/0.92  fof(f25,plain,(
% 3.59/0.92    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 3.59/0.92    inference(ennf_transformation,[],[f10])).
% 3.59/0.92  fof(f10,axiom,(
% 3.59/0.92    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 3.59/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 3.59/0.92  fof(f357,plain,(
% 3.59/0.92    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k8_relat_1(X2,k6_relat_1(X1))) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X2))) )),
% 3.59/0.92    inference(forward_demodulation,[],[f352,f78])).
% 3.59/0.92  fof(f352,plain,(
% 3.59/0.92    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k8_relat_1(X2,k6_relat_1(X1)))) )),
% 3.59/0.92    inference(resolution,[],[f142,f38])).
% 3.59/0.92  fof(f142,plain,(
% 3.59/0.92    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k8_relat_1(X2,k6_relat_1(X1)))) )),
% 3.59/0.92    inference(forward_demodulation,[],[f139,f78])).
% 3.59/0.92  fof(f139,plain,(
% 3.59/0.92    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 3.59/0.92    inference(resolution,[],[f102,f38])).
% 3.59/0.92  fof(f102,plain,(
% 3.59/0.92    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 3.59/0.92    inference(resolution,[],[f42,f38])).
% 3.59/0.92  fof(f42,plain,(
% 3.59/0.92    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.59/0.92    inference(cnf_transformation,[],[f23])).
% 3.59/0.92  fof(f23,plain,(
% 3.59/0.92    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.59/0.92    inference(ennf_transformation,[],[f12])).
% 3.59/0.92  fof(f12,axiom,(
% 3.59/0.92    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 3.59/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 3.59/0.92  fof(f721,plain,(
% 3.59/0.92    ( ! [X14,X15,X13] : (k5_relat_1(k6_relat_1(X15),k8_relat_1(X13,k6_relat_1(X14))) = k7_relat_1(k8_relat_1(X13,k6_relat_1(X14)),X15)) )),
% 3.59/0.92    inference(superposition,[],[f84,f271])).
% 3.59/0.92  fof(f84,plain,(
% 3.59/0.92    ( ! [X4,X2,X3] : (k5_relat_1(k6_relat_1(X2),k3_xboole_0(k6_relat_1(X3),X4)) = k7_relat_1(k3_xboole_0(k6_relat_1(X3),X4),X2)) )),
% 3.59/0.92    inference(resolution,[],[f50,f62])).
% 3.59/0.92  fof(f1203,plain,(
% 3.59/0.92    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k3_xboole_0(X0,X1))) )),
% 3.59/0.92    inference(forward_demodulation,[],[f1191,f93])).
% 3.59/0.92  fof(f1191,plain,(
% 3.59/0.92    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) )),
% 3.59/0.92    inference(superposition,[],[f367,f271])).
% 3.59/0.92  fof(f367,plain,(
% 3.59/0.92    ( ! [X0,X1] : (k3_xboole_0(k6_relat_1(X0),X1) = k7_relat_1(k3_xboole_0(k6_relat_1(X0),X1),k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)))) )),
% 3.59/0.92    inference(resolution,[],[f101,f60])).
% 3.59/0.92  fof(f60,plain,(
% 3.59/0.92    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.59/0.92    inference(equality_resolution,[],[f57])).
% 3.59/0.92  fof(f57,plain,(
% 3.59/0.92    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.59/0.92    inference(cnf_transformation,[],[f36])).
% 3.59/0.92  fof(f36,plain,(
% 3.59/0.92    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.92    inference(flattening,[],[f35])).
% 3.59/0.92  fof(f35,plain,(
% 3.59/0.92    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.59/0.92    inference(nnf_transformation,[],[f2])).
% 3.59/0.92  fof(f2,axiom,(
% 3.59/0.92    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.59/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.59/0.92  fof(f101,plain,(
% 3.59/0.92    ( ! [X4,X2,X3] : (~r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X2),X3)),X4) | k3_xboole_0(k6_relat_1(X2),X3) = k7_relat_1(k3_xboole_0(k6_relat_1(X2),X3),X4)) )),
% 3.59/0.92    inference(forward_demodulation,[],[f98,f84])).
% 3.59/0.92  fof(f98,plain,(
% 3.59/0.92    ( ! [X4,X2,X3] : (~r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X2),X3)),X4) | k3_xboole_0(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X4),k3_xboole_0(k6_relat_1(X2),X3))) )),
% 3.59/0.92    inference(resolution,[],[f55,f62])).
% 3.59/0.92  fof(f55,plain,(
% 3.59/0.92    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 3.59/0.92    inference(cnf_transformation,[],[f32])).
% 3.59/0.92  fof(f32,plain,(
% 3.59/0.92    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.59/0.92    inference(flattening,[],[f31])).
% 3.59/0.92  fof(f31,plain,(
% 3.59/0.92    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.59/0.92    inference(ennf_transformation,[],[f15])).
% 3.59/0.92  fof(f15,axiom,(
% 3.59/0.92    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.59/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 3.59/0.92  fof(f78,plain,(
% 3.59/0.92    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 3.59/0.92    inference(resolution,[],[f49,f38])).
% 3.59/0.92  fof(f37,plain,(
% 3.59/0.92    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.59/0.92    inference(cnf_transformation,[],[f34])).
% 3.59/0.92  fof(f34,plain,(
% 3.59/0.92    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.59/0.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f33])).
% 3.59/0.92  fof(f33,plain,(
% 3.59/0.92    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.59/0.92    introduced(choice_axiom,[])).
% 3.59/0.92  fof(f21,plain,(
% 3.59/0.92    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.59/0.92    inference(ennf_transformation,[],[f20])).
% 3.59/0.92  fof(f20,negated_conjecture,(
% 3.59/0.92    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.59/0.92    inference(negated_conjecture,[],[f19])).
% 3.59/0.92  fof(f19,conjecture,(
% 3.59/0.92    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.59/0.92    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 3.59/0.92  % SZS output end Proof for theBenchmark
% 3.59/0.92  % (18519)------------------------------
% 3.59/0.92  % (18519)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.59/0.92  % (18519)Termination reason: Refutation
% 3.59/0.92  
% 3.59/0.92  % (18519)Memory used [KB]: 5245
% 3.59/0.92  % (18519)Time elapsed: 0.470 s
% 3.59/0.92  % (18519)------------------------------
% 3.59/0.92  % (18519)------------------------------
% 3.90/0.94  % (18511)Success in time 0.581 s
%------------------------------------------------------------------------------

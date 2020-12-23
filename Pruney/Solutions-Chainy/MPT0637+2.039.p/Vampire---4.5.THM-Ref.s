%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:52:27 EST 2020

% Result     : Theorem 3.05s
% Output     : Refutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 336 expanded)
%              Number of leaves         :   15 (  86 expanded)
%              Depth                    :   16
%              Number of atoms          :  152 ( 558 expanded)
%              Number of equality atoms :   73 ( 214 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5080,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f4984])).

fof(f4984,plain,(
    k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(superposition,[],[f81,f4279])).

fof(f4279,plain,(
    ! [X2,X1] : k6_relat_1(k3_xboole_0(X1,X2)) = k8_relat_1(X1,k6_relat_1(X2)) ),
    inference(backward_demodulation,[],[f128,f4278])).

fof(f4278,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k6_relat_1(k3_xboole_0(X2,X3))) ),
    inference(forward_demodulation,[],[f4226,f129])).

fof(f129,plain,(
    ! [X4,X3] : k6_relat_1(k3_xboole_0(X3,X4)) = k8_relat_1(X4,k6_relat_1(k3_xboole_0(X3,X4))) ),
    inference(resolution,[],[f98,f64])).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f44,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

% (16777)Refutation not found, incomplete strategy% (16777)------------------------------
% (16777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (16777)Termination reason: Refutation not found, incomplete strategy

% (16777)Memory used [KB]: 6140
% (16777)Time elapsed: 0.176 s
% (16777)------------------------------
% (16777)------------------------------
fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(forward_demodulation,[],[f96,f41])).

fof(f41,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(resolution,[],[f55,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f4226,plain,(
    ! [X2,X3] : k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(k3_xboole_0(X2,X3)))) ),
    inference(superposition,[],[f1204,f747])).

fof(f747,plain,(
    ! [X14,X15,X13] : k7_relat_1(k8_relat_1(X13,k6_relat_1(X14)),X15) = k8_relat_1(X13,k8_relat_1(X14,k6_relat_1(X15))) ),
    inference(forward_demodulation,[],[f722,f746])).

fof(f746,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k8_relat_1(X2,k6_relat_1(X1))) = k8_relat_1(X2,k8_relat_1(X1,k6_relat_1(X0))) ),
    inference(backward_demodulation,[],[f358,f720])).

fof(f720,plain,(
    ! [X8,X7,X9] : k8_relat_1(X9,k8_relat_1(X7,k6_relat_1(X8))) = k5_relat_1(k8_relat_1(X7,k6_relat_1(X8)),k6_relat_1(X9)) ),
    inference(superposition,[],[f80,f272])).

fof(f272,plain,(
    ! [X4,X5] : k8_relat_1(X4,k6_relat_1(X5)) = k3_xboole_0(k6_relat_1(X4),k8_relat_1(X4,k6_relat_1(X5))) ),
    inference(forward_demodulation,[],[f269,f40])).

fof(f40,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f12])).

fof(f269,plain,(
    ! [X4,X5] : k3_xboole_0(k6_relat_1(X4),k8_relat_1(X4,k6_relat_1(X5))) = k1_relat_1(k6_relat_1(k8_relat_1(X4,k6_relat_1(X5)))) ),
    inference(superposition,[],[f95,f130])).

fof(f130,plain,(
    ! [X6,X5] : k6_relat_1(k8_relat_1(X5,k6_relat_1(X6))) = k8_relat_1(k6_relat_1(X5),k6_relat_1(k8_relat_1(X5,k6_relat_1(X6)))) ),
    inference(resolution,[],[f98,f82])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X1)) ),
    inference(backward_demodulation,[],[f71,f79])).

fof(f79,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1)) ),
    inference(resolution,[],[f50,f39])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X1)) ),
    inference(resolution,[],[f54,f39])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f95,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))) ),
    inference(forward_demodulation,[],[f94,f87])).

fof(f87,plain,(
    ! [X0,X1] : k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(forward_demodulation,[],[f85,f79])).

fof(f85,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f51,f39])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f94,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f92,f40])).

fof(f92,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) ),
    inference(resolution,[],[f52,f39])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

fof(f80,plain,(
    ! [X4,X2,X3] : k8_relat_1(X2,k3_xboole_0(k6_relat_1(X3),X4)) = k5_relat_1(k3_xboole_0(k6_relat_1(X3),X4),k6_relat_1(X2)) ),
    inference(resolution,[],[f50,f63])).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)) ),
    inference(resolution,[],[f49,f39])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f358,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k8_relat_1(X2,k6_relat_1(X1))) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f353,f79])).

fof(f353,plain,(
    ! [X2,X0,X1] : k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k8_relat_1(X2,k6_relat_1(X1))) ),
    inference(resolution,[],[f143,f39])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k8_relat_1(X2,k6_relat_1(X1))) ) ),
    inference(forward_demodulation,[],[f140,f79])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f104,f39])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f43,f39])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f722,plain,(
    ! [X14,X15,X13] : k5_relat_1(k6_relat_1(X15),k8_relat_1(X13,k6_relat_1(X14))) = k7_relat_1(k8_relat_1(X13,k6_relat_1(X14)),X15) ),
    inference(superposition,[],[f86,f272])).

fof(f86,plain,(
    ! [X4,X2,X3] : k5_relat_1(k6_relat_1(X2),k3_xboole_0(k6_relat_1(X3),X4)) = k7_relat_1(k3_xboole_0(k6_relat_1(X3),X4),X2) ),
    inference(resolution,[],[f51,f63])).

fof(f1204,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k3_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f1192,f95])).

fof(f1192,plain,(
    ! [X0,X1] : k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) ),
    inference(superposition,[],[f368,f272])).

fof(f368,plain,(
    ! [X0,X1] : k3_xboole_0(k6_relat_1(X0),X1) = k7_relat_1(k3_xboole_0(k6_relat_1(X0),X1),k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1))) ),
    inference(resolution,[],[f103,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
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

fof(f103,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X2),X3)),X4)
      | k3_xboole_0(k6_relat_1(X2),X3) = k7_relat_1(k3_xboole_0(k6_relat_1(X2),X3),X4) ) ),
    inference(forward_demodulation,[],[f100,f86])).

fof(f100,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X2),X3)),X4)
      | k3_xboole_0(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X4),k3_xboole_0(k6_relat_1(X2),X3)) ) ),
    inference(resolution,[],[f56,f63])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | k5_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = X1
      | ~ r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f128,plain,(
    ! [X2,X1] : k6_relat_1(k3_xboole_0(X1,X2)) = k8_relat_1(X1,k6_relat_1(k3_xboole_0(X1,X2))) ),
    inference(resolution,[],[f98,f44])).

fof(f81,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f38,f79])).

fof(f38,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f34])).

fof(f34,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:04:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (16714)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (16733)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (16725)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (16725)Refutation not found, incomplete strategy% (16725)------------------------------
% 0.22/0.51  % (16725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (16725)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (16725)Memory used [KB]: 1663
% 0.22/0.51  % (16725)Time elapsed: 0.053 s
% 0.22/0.51  % (16725)------------------------------
% 0.22/0.51  % (16725)------------------------------
% 0.22/0.52  % (16718)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (16716)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.23/0.53  % (16729)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.23/0.53  % (16722)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.23/0.53  % (16722)Refutation not found, incomplete strategy% (16722)------------------------------
% 1.23/0.53  % (16722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (16722)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  % (16729)Refutation not found, incomplete strategy% (16729)------------------------------
% 1.23/0.53  % (16729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  
% 1.23/0.53  % (16722)Memory used [KB]: 6140
% 1.23/0.53  % (16722)Time elapsed: 0.105 s
% 1.23/0.53  % (16722)------------------------------
% 1.23/0.53  % (16722)------------------------------
% 1.23/0.53  % (16729)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (16729)Memory used [KB]: 1663
% 1.23/0.53  % (16729)Time elapsed: 0.103 s
% 1.23/0.53  % (16729)------------------------------
% 1.23/0.53  % (16729)------------------------------
% 1.23/0.53  % (16712)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.23/0.53  % (16712)Refutation not found, incomplete strategy% (16712)------------------------------
% 1.23/0.53  % (16712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (16712)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (16712)Memory used [KB]: 1663
% 1.23/0.53  % (16712)Time elapsed: 0.114 s
% 1.23/0.53  % (16712)------------------------------
% 1.23/0.53  % (16712)------------------------------
% 1.23/0.54  % (16727)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.40/0.54  % (16740)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.40/0.54  % (16715)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.40/0.54  % (16739)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.40/0.55  % (16738)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.40/0.55  % (16731)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.40/0.55  % (16730)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.40/0.55  % (16720)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.40/0.55  % (16713)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.40/0.55  % (16728)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.40/0.55  % (16721)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.40/0.55  % (16711)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.40/0.55  % (16738)Refutation not found, incomplete strategy% (16738)------------------------------
% 1.40/0.55  % (16738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (16738)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (16738)Memory used [KB]: 6140
% 1.40/0.55  % (16738)Time elapsed: 0.141 s
% 1.40/0.55  % (16738)------------------------------
% 1.40/0.55  % (16738)------------------------------
% 1.40/0.55  % (16728)Refutation not found, incomplete strategy% (16728)------------------------------
% 1.40/0.55  % (16728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (16728)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (16728)Memory used [KB]: 1663
% 1.40/0.55  % (16728)Time elapsed: 0.136 s
% 1.40/0.55  % (16728)------------------------------
% 1.40/0.55  % (16728)------------------------------
% 1.40/0.56  % (16740)Refutation not found, incomplete strategy% (16740)------------------------------
% 1.40/0.56  % (16740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (16740)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (16740)Memory used [KB]: 1663
% 1.40/0.56  % (16740)Time elapsed: 0.002 s
% 1.40/0.56  % (16740)------------------------------
% 1.40/0.56  % (16740)------------------------------
% 1.40/0.56  % (16727)Refutation not found, incomplete strategy% (16727)------------------------------
% 1.40/0.56  % (16727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (16727)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (16727)Memory used [KB]: 10618
% 1.40/0.56  % (16727)Time elapsed: 0.137 s
% 1.40/0.56  % (16727)------------------------------
% 1.40/0.56  % (16727)------------------------------
% 1.40/0.56  % (16723)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.40/0.56  % (16736)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.40/0.56  % (16721)Refutation not found, incomplete strategy% (16721)------------------------------
% 1.40/0.56  % (16721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (16721)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (16721)Memory used [KB]: 10618
% 1.40/0.56  % (16721)Time elapsed: 0.137 s
% 1.40/0.56  % (16721)------------------------------
% 1.40/0.56  % (16721)------------------------------
% 1.40/0.56  % (16723)Refutation not found, incomplete strategy% (16723)------------------------------
% 1.40/0.56  % (16723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (16723)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (16723)Memory used [KB]: 10618
% 1.40/0.56  % (16723)Time elapsed: 0.147 s
% 1.40/0.56  % (16723)------------------------------
% 1.40/0.56  % (16723)------------------------------
% 1.40/0.56  % (16736)Refutation not found, incomplete strategy% (16736)------------------------------
% 1.40/0.56  % (16736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.56  % (16736)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.56  
% 1.40/0.56  % (16736)Memory used [KB]: 6140
% 1.40/0.56  % (16736)Time elapsed: 0.150 s
% 1.40/0.56  % (16736)------------------------------
% 1.40/0.56  % (16736)------------------------------
% 1.40/0.56  % (16735)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.40/0.57  % (16735)Refutation not found, incomplete strategy% (16735)------------------------------
% 1.40/0.57  % (16735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (16735)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (16735)Memory used [KB]: 10618
% 1.40/0.57  % (16735)Time elapsed: 0.149 s
% 1.40/0.57  % (16735)------------------------------
% 1.40/0.57  % (16735)------------------------------
% 1.40/0.57  % (16739)Refutation not found, incomplete strategy% (16739)------------------------------
% 1.40/0.57  % (16739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.57  % (16739)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.57  
% 1.40/0.57  % (16739)Memory used [KB]: 10618
% 1.40/0.57  % (16739)Time elapsed: 0.147 s
% 1.40/0.57  % (16739)------------------------------
% 1.40/0.57  % (16739)------------------------------
% 1.40/0.57  % (16732)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.40/0.57  % (16717)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.58  % (16724)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.40/0.58  % (16719)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.40/0.58  % (16726)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.40/0.59  % (16734)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.40/0.60  % (16737)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.40/0.60  % (16737)Refutation not found, incomplete strategy% (16737)------------------------------
% 1.40/0.60  % (16737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.60  % (16737)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.60  
% 1.40/0.60  % (16737)Memory used [KB]: 6140
% 1.40/0.60  % (16737)Time elapsed: 0.179 s
% 1.40/0.60  % (16737)------------------------------
% 1.40/0.60  % (16737)------------------------------
% 1.90/0.64  % (16763)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.90/0.65  % (16714)Refutation not found, incomplete strategy% (16714)------------------------------
% 1.90/0.65  % (16714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.65  % (16762)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.90/0.65  % (16714)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.65  
% 1.90/0.65  % (16714)Memory used [KB]: 6140
% 1.90/0.65  % (16714)Time elapsed: 0.223 s
% 1.90/0.65  % (16714)------------------------------
% 1.90/0.65  % (16714)------------------------------
% 1.90/0.66  % (16770)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 1.90/0.67  % (16764)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 1.90/0.67  % (16766)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 1.90/0.67  % (16766)Refutation not found, incomplete strategy% (16766)------------------------------
% 1.90/0.67  % (16766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.67  % (16766)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.67  
% 1.90/0.67  % (16766)Memory used [KB]: 10618
% 1.90/0.67  % (16766)Time elapsed: 0.058 s
% 1.90/0.67  % (16766)------------------------------
% 1.90/0.67  % (16766)------------------------------
% 1.90/0.67  % (16765)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 1.90/0.67  % (16765)Refutation not found, incomplete strategy% (16765)------------------------------
% 1.90/0.67  % (16765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.67  % (16765)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.67  
% 1.90/0.67  % (16765)Memory used [KB]: 10618
% 1.90/0.67  % (16765)Time elapsed: 0.109 s
% 1.90/0.67  % (16765)------------------------------
% 1.90/0.67  % (16765)------------------------------
% 1.90/0.68  % (16772)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 1.90/0.68  % (16767)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.90/0.68  % (16767)Refutation not found, incomplete strategy% (16767)------------------------------
% 1.90/0.68  % (16767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.68  % (16767)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.68  
% 1.90/0.68  % (16767)Memory used [KB]: 1663
% 1.90/0.68  % (16767)Time elapsed: 0.095 s
% 1.90/0.68  % (16767)------------------------------
% 1.90/0.68  % (16767)------------------------------
% 1.90/0.68  % (16768)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 1.90/0.69  % (16768)Refutation not found, incomplete strategy% (16768)------------------------------
% 1.90/0.69  % (16768)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.90/0.69  % (16768)Termination reason: Refutation not found, incomplete strategy
% 1.90/0.69  
% 1.90/0.69  % (16768)Memory used [KB]: 10618
% 1.90/0.69  % (16768)Time elapsed: 0.096 s
% 1.90/0.69  % (16768)------------------------------
% 1.90/0.69  % (16768)------------------------------
% 2.27/0.69  % (16771)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.27/0.69  % (16771)Refutation not found, incomplete strategy% (16771)------------------------------
% 2.27/0.69  % (16771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.69  % (16771)Termination reason: Refutation not found, incomplete strategy
% 2.27/0.69  
% 2.27/0.69  % (16771)Memory used [KB]: 10618
% 2.27/0.69  % (16771)Time elapsed: 0.104 s
% 2.27/0.69  % (16771)------------------------------
% 2.27/0.69  % (16771)------------------------------
% 2.27/0.70  % (16713)Refutation not found, incomplete strategy% (16713)------------------------------
% 2.27/0.70  % (16713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.70  % (16713)Termination reason: Refutation not found, incomplete strategy
% 2.27/0.70  
% 2.27/0.70  % (16713)Memory used [KB]: 6140
% 2.27/0.70  % (16713)Time elapsed: 0.275 s
% 2.27/0.70  % (16713)------------------------------
% 2.27/0.70  % (16713)------------------------------
% 2.27/0.70  % (16774)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.27/0.71  % (16769)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.27/0.73  % (16773)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.27/0.73  % (16726)Refutation not found, incomplete strategy% (16726)------------------------------
% 2.27/0.73  % (16726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.73  % (16726)Termination reason: Refutation not found, incomplete strategy
% 2.27/0.73  
% 2.27/0.73  % (16726)Memory used [KB]: 6140
% 2.27/0.73  % (16726)Time elapsed: 0.287 s
% 2.27/0.73  % (16726)------------------------------
% 2.27/0.73  % (16726)------------------------------
% 2.27/0.73  % (16773)Refutation not found, incomplete strategy% (16773)------------------------------
% 2.27/0.73  % (16773)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.73  % (16773)Termination reason: Refutation not found, incomplete strategy
% 2.27/0.73  
% 2.27/0.73  % (16773)Memory used [KB]: 10618
% 2.27/0.73  % (16773)Time elapsed: 0.126 s
% 2.27/0.73  % (16773)------------------------------
% 2.27/0.73  % (16773)------------------------------
% 2.27/0.75  % (16719)Refutation not found, incomplete strategy% (16719)------------------------------
% 2.27/0.75  % (16719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.27/0.75  % (16719)Termination reason: Refutation not found, incomplete strategy
% 2.27/0.75  
% 2.27/0.75  % (16719)Memory used [KB]: 6140
% 2.27/0.75  % (16719)Time elapsed: 0.338 s
% 2.27/0.75  % (16719)------------------------------
% 2.27/0.75  % (16719)------------------------------
% 2.66/0.77  % (16775)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.66/0.77  % (16775)Refutation not found, incomplete strategy% (16775)------------------------------
% 2.66/0.77  % (16775)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.66/0.77  % (16775)Termination reason: Refutation not found, incomplete strategy
% 2.66/0.77  
% 2.66/0.77  % (16775)Memory used [KB]: 10618
% 2.66/0.77  % (16775)Time elapsed: 0.143 s
% 2.66/0.77  % (16775)------------------------------
% 2.66/0.77  % (16775)------------------------------
% 2.66/0.79  % (16776)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 2.66/0.80  % (16770)Refutation not found, incomplete strategy% (16770)------------------------------
% 2.66/0.80  % (16770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.66/0.80  % (16770)Termination reason: Refutation not found, incomplete strategy
% 2.66/0.80  
% 2.66/0.80  % (16770)Memory used [KB]: 6268
% 2.66/0.80  % (16770)Time elapsed: 0.169 s
% 2.66/0.80  % (16770)------------------------------
% 2.66/0.80  % (16770)------------------------------
% 2.83/0.81  % (16777)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 2.83/0.81  % (16779)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 2.83/0.82  % (16780)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 2.83/0.83  % (16782)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 2.83/0.83  % (16778)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 2.83/0.83  % (16781)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 2.83/0.83  % (16781)Refutation not found, incomplete strategy% (16781)------------------------------
% 2.83/0.83  % (16781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.83/0.83  % (16781)Termination reason: Refutation not found, incomplete strategy
% 2.83/0.83  
% 2.83/0.83  % (16781)Memory used [KB]: 1663
% 2.83/0.83  % (16781)Time elapsed: 0.115 s
% 2.83/0.83  % (16781)------------------------------
% 2.83/0.83  % (16781)------------------------------
% 3.05/0.88  % (16718)Refutation found. Thanks to Tanya!
% 3.05/0.88  % SZS status Theorem for theBenchmark
% 3.05/0.88  % SZS output start Proof for theBenchmark
% 3.05/0.88  fof(f5080,plain,(
% 3.05/0.88    $false),
% 3.05/0.88    inference(trivial_inequality_removal,[],[f4984])).
% 3.05/0.88  fof(f4984,plain,(
% 3.05/0.88    k8_relat_1(sK0,k6_relat_1(sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 3.05/0.88    inference(superposition,[],[f81,f4279])).
% 3.05/0.88  fof(f4279,plain,(
% 3.05/0.88    ( ! [X2,X1] : (k6_relat_1(k3_xboole_0(X1,X2)) = k8_relat_1(X1,k6_relat_1(X2))) )),
% 3.05/0.88    inference(backward_demodulation,[],[f128,f4278])).
% 3.05/0.88  fof(f4278,plain,(
% 3.05/0.88    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k6_relat_1(k3_xboole_0(X2,X3)))) )),
% 3.05/0.88    inference(forward_demodulation,[],[f4226,f129])).
% 3.05/0.88  fof(f129,plain,(
% 3.05/0.88    ( ! [X4,X3] : (k6_relat_1(k3_xboole_0(X3,X4)) = k8_relat_1(X4,k6_relat_1(k3_xboole_0(X3,X4)))) )),
% 3.05/0.88    inference(resolution,[],[f98,f64])).
% 3.05/0.88  fof(f64,plain,(
% 3.05/0.88    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 3.05/0.88    inference(superposition,[],[f44,f45])).
% 3.05/0.88  fof(f45,plain,(
% 3.05/0.88    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.05/0.88    inference(cnf_transformation,[],[f1])).
% 3.05/0.88  fof(f1,axiom,(
% 3.05/0.88    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.05/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.05/0.88  fof(f44,plain,(
% 3.05/0.88    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.05/0.88    inference(cnf_transformation,[],[f3])).
% 3.05/0.88  % (16777)Refutation not found, incomplete strategy% (16777)------------------------------
% 3.05/0.88  % (16777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.88  % (16777)Termination reason: Refutation not found, incomplete strategy
% 3.05/0.88  
% 3.05/0.88  % (16777)Memory used [KB]: 6140
% 3.05/0.88  % (16777)Time elapsed: 0.176 s
% 3.05/0.88  % (16777)------------------------------
% 3.05/0.88  % (16777)------------------------------
% 3.05/0.89  fof(f3,axiom,(
% 3.05/0.89    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.05/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.05/0.89  fof(f98,plain,(
% 3.05/0.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 3.05/0.89    inference(forward_demodulation,[],[f96,f41])).
% 3.05/0.89  fof(f41,plain,(
% 3.05/0.89    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 3.05/0.89    inference(cnf_transformation,[],[f12])).
% 3.05/0.89  fof(f12,axiom,(
% 3.05/0.89    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.05/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 3.05/0.89  fof(f96,plain,(
% 3.05/0.89    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k8_relat_1(X1,k6_relat_1(X0))) )),
% 3.05/0.89    inference(resolution,[],[f55,f39])).
% 3.05/0.89  fof(f39,plain,(
% 3.05/0.89    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 3.05/0.89    inference(cnf_transformation,[],[f21])).
% 3.05/0.89  fof(f21,plain,(
% 3.05/0.89    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 3.05/0.89    inference(pure_predicate_removal,[],[f18])).
% 3.05/0.89  fof(f18,axiom,(
% 3.05/0.89    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.05/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).
% 3.05/0.89  fof(f55,plain,(
% 3.05/0.89    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k8_relat_1(X0,X1) = X1) )),
% 3.05/0.89    inference(cnf_transformation,[],[f31])).
% 3.05/0.89  fof(f31,plain,(
% 3.05/0.89    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.05/0.89    inference(flattening,[],[f30])).
% 3.05/0.89  fof(f30,plain,(
% 3.05/0.89    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.05/0.89    inference(ennf_transformation,[],[f10])).
% 3.05/0.89  fof(f10,axiom,(
% 3.05/0.89    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 3.05/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 3.05/0.89  fof(f4226,plain,(
% 3.05/0.89    ( ! [X2,X3] : (k8_relat_1(X2,k6_relat_1(X3)) = k8_relat_1(X2,k8_relat_1(X3,k6_relat_1(k3_xboole_0(X2,X3))))) )),
% 3.05/0.89    inference(superposition,[],[f1204,f747])).
% 3.05/0.89  fof(f747,plain,(
% 3.05/0.89    ( ! [X14,X15,X13] : (k7_relat_1(k8_relat_1(X13,k6_relat_1(X14)),X15) = k8_relat_1(X13,k8_relat_1(X14,k6_relat_1(X15)))) )),
% 3.05/0.89    inference(forward_demodulation,[],[f722,f746])).
% 3.05/0.89  fof(f746,plain,(
% 3.05/0.89    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k8_relat_1(X2,k6_relat_1(X1))) = k8_relat_1(X2,k8_relat_1(X1,k6_relat_1(X0)))) )),
% 3.05/0.89    inference(backward_demodulation,[],[f358,f720])).
% 3.05/0.89  fof(f720,plain,(
% 3.05/0.89    ( ! [X8,X7,X9] : (k8_relat_1(X9,k8_relat_1(X7,k6_relat_1(X8))) = k5_relat_1(k8_relat_1(X7,k6_relat_1(X8)),k6_relat_1(X9))) )),
% 3.05/0.89    inference(superposition,[],[f80,f272])).
% 3.05/0.89  fof(f272,plain,(
% 3.05/0.89    ( ! [X4,X5] : (k8_relat_1(X4,k6_relat_1(X5)) = k3_xboole_0(k6_relat_1(X4),k8_relat_1(X4,k6_relat_1(X5)))) )),
% 3.05/0.89    inference(forward_demodulation,[],[f269,f40])).
% 3.05/0.89  fof(f40,plain,(
% 3.05/0.89    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.05/0.89    inference(cnf_transformation,[],[f12])).
% 3.05/0.89  fof(f269,plain,(
% 3.05/0.89    ( ! [X4,X5] : (k3_xboole_0(k6_relat_1(X4),k8_relat_1(X4,k6_relat_1(X5))) = k1_relat_1(k6_relat_1(k8_relat_1(X4,k6_relat_1(X5))))) )),
% 3.05/0.89    inference(superposition,[],[f95,f130])).
% 3.05/0.89  fof(f130,plain,(
% 3.05/0.89    ( ! [X6,X5] : (k6_relat_1(k8_relat_1(X5,k6_relat_1(X6))) = k8_relat_1(k6_relat_1(X5),k6_relat_1(k8_relat_1(X5,k6_relat_1(X6))))) )),
% 3.05/0.89    inference(resolution,[],[f98,f82])).
% 3.05/0.89  fof(f82,plain,(
% 3.05/0.89    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X1))) )),
% 3.05/0.89    inference(backward_demodulation,[],[f71,f79])).
% 3.05/0.89  fof(f79,plain,(
% 3.05/0.89    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k8_relat_1(X0,k6_relat_1(X1))) )),
% 3.05/0.89    inference(resolution,[],[f50,f39])).
% 3.05/0.89  fof(f50,plain,(
% 3.05/0.89    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 3.05/0.89    inference(cnf_transformation,[],[f26])).
% 3.05/0.89  fof(f26,plain,(
% 3.05/0.89    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 3.05/0.89    inference(ennf_transformation,[],[f9])).
% 3.05/0.89  fof(f9,axiom,(
% 3.05/0.89    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 3.05/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).
% 3.05/0.89  fof(f71,plain,(
% 3.05/0.89    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X1))) )),
% 3.05/0.89    inference(resolution,[],[f54,f39])).
% 3.05/0.89  fof(f54,plain,(
% 3.05/0.89    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)) )),
% 3.05/0.89    inference(cnf_transformation,[],[f29])).
% 3.05/0.89  fof(f29,plain,(
% 3.05/0.89    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 3.05/0.89    inference(ennf_transformation,[],[f13])).
% 3.05/0.89  fof(f13,axiom,(
% 3.05/0.89    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 3.05/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 3.05/0.89  fof(f95,plain,(
% 3.05/0.89    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k8_relat_1(X0,k6_relat_1(X1)))) )),
% 3.05/0.89    inference(forward_demodulation,[],[f94,f87])).
% 3.05/0.89  fof(f87,plain,(
% 3.05/0.89    ( ! [X0,X1] : (k8_relat_1(X1,k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 3.05/0.89    inference(forward_demodulation,[],[f85,f79])).
% 3.05/0.89  fof(f85,plain,(
% 3.05/0.89    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 3.05/0.89    inference(resolution,[],[f51,f39])).
% 3.05/0.89  fof(f51,plain,(
% 3.05/0.89    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 3.05/0.89    inference(cnf_transformation,[],[f27])).
% 3.05/0.89  fof(f27,plain,(
% 3.05/0.89    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.05/0.89    inference(ennf_transformation,[],[f17])).
% 3.05/0.89  fof(f17,axiom,(
% 3.05/0.89    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 3.05/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 3.05/0.89  fof(f94,plain,(
% 3.05/0.89    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 3.05/0.89    inference(forward_demodulation,[],[f92,f40])).
% 3.05/0.89  fof(f92,plain,(
% 3.05/0.89    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) )),
% 3.05/0.89    inference(resolution,[],[f52,f39])).
% 3.05/0.89  fof(f52,plain,(
% 3.05/0.89    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 3.05/0.89    inference(cnf_transformation,[],[f28])).
% 3.05/0.89  fof(f28,plain,(
% 3.05/0.89    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.05/0.89    inference(ennf_transformation,[],[f16])).
% 3.05/0.89  fof(f16,axiom,(
% 3.05/0.89    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 3.05/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 3.05/0.89  fof(f80,plain,(
% 3.05/0.89    ( ! [X4,X2,X3] : (k8_relat_1(X2,k3_xboole_0(k6_relat_1(X3),X4)) = k5_relat_1(k3_xboole_0(k6_relat_1(X3),X4),k6_relat_1(X2))) )),
% 3.05/0.89    inference(resolution,[],[f50,f63])).
% 3.05/0.89  fof(f63,plain,(
% 3.05/0.89    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(k6_relat_1(X0),X1))) )),
% 3.05/0.89    inference(resolution,[],[f49,f39])).
% 3.05/0.89  fof(f49,plain,(
% 3.05/0.89    ( ! [X0,X1] : (~v1_relat_1(X0) | v1_relat_1(k3_xboole_0(X0,X1))) )),
% 3.05/0.89    inference(cnf_transformation,[],[f25])).
% 3.05/0.89  fof(f25,plain,(
% 3.05/0.89    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 3.05/0.89    inference(ennf_transformation,[],[f8])).
% 3.05/0.89  fof(f8,axiom,(
% 3.05/0.89    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 3.05/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 3.05/0.89  fof(f358,plain,(
% 3.05/0.89    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k8_relat_1(X2,k6_relat_1(X1))) = k5_relat_1(k8_relat_1(X1,k6_relat_1(X0)),k6_relat_1(X2))) )),
% 3.05/0.89    inference(forward_demodulation,[],[f353,f79])).
% 3.05/0.89  fof(f353,plain,(
% 3.05/0.89    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(k6_relat_1(X0),k8_relat_1(X2,k6_relat_1(X1)))) )),
% 3.05/0.89    inference(resolution,[],[f143,f39])).
% 3.05/0.89  fof(f143,plain,(
% 3.05/0.89    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k8_relat_1(X2,k6_relat_1(X1)))) )),
% 3.05/0.89    inference(forward_demodulation,[],[f140,f79])).
% 3.05/0.89  fof(f140,plain,(
% 3.05/0.89    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 3.05/0.89    inference(resolution,[],[f104,f39])).
% 3.05/0.89  fof(f104,plain,(
% 3.05/0.89    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 3.05/0.89    inference(resolution,[],[f43,f39])).
% 3.05/0.89  fof(f43,plain,(
% 3.05/0.89    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 3.05/0.89    inference(cnf_transformation,[],[f24])).
% 3.05/0.89  fof(f24,plain,(
% 3.05/0.89    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 3.05/0.89    inference(ennf_transformation,[],[f11])).
% 3.05/0.89  fof(f11,axiom,(
% 3.05/0.89    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 3.05/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 3.05/0.89  fof(f722,plain,(
% 3.05/0.89    ( ! [X14,X15,X13] : (k5_relat_1(k6_relat_1(X15),k8_relat_1(X13,k6_relat_1(X14))) = k7_relat_1(k8_relat_1(X13,k6_relat_1(X14)),X15)) )),
% 3.05/0.89    inference(superposition,[],[f86,f272])).
% 3.05/0.89  fof(f86,plain,(
% 3.05/0.89    ( ! [X4,X2,X3] : (k5_relat_1(k6_relat_1(X2),k3_xboole_0(k6_relat_1(X3),X4)) = k7_relat_1(k3_xboole_0(k6_relat_1(X3),X4),X2)) )),
% 3.05/0.89    inference(resolution,[],[f51,f63])).
% 3.05/0.89  fof(f1204,plain,(
% 3.05/0.89    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k3_xboole_0(X0,X1))) )),
% 3.05/0.89    inference(forward_demodulation,[],[f1192,f95])).
% 3.05/0.89  fof(f1192,plain,(
% 3.05/0.89    ( ! [X0,X1] : (k8_relat_1(X0,k6_relat_1(X1)) = k7_relat_1(k8_relat_1(X0,k6_relat_1(X1)),k1_relat_1(k8_relat_1(X0,k6_relat_1(X1))))) )),
% 3.05/0.89    inference(superposition,[],[f368,f272])).
% 3.05/0.89  fof(f368,plain,(
% 3.05/0.89    ( ! [X0,X1] : (k3_xboole_0(k6_relat_1(X0),X1) = k7_relat_1(k3_xboole_0(k6_relat_1(X0),X1),k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)))) )),
% 3.05/0.89    inference(resolution,[],[f103,f61])).
% 3.05/0.89  fof(f61,plain,(
% 3.05/0.89    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.05/0.89    inference(equality_resolution,[],[f58])).
% 3.05/0.89  fof(f58,plain,(
% 3.05/0.89    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.05/0.89    inference(cnf_transformation,[],[f37])).
% 3.05/0.89  fof(f37,plain,(
% 3.05/0.89    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.05/0.89    inference(flattening,[],[f36])).
% 3.05/0.89  fof(f36,plain,(
% 3.05/0.89    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.05/0.89    inference(nnf_transformation,[],[f2])).
% 3.05/0.89  fof(f2,axiom,(
% 3.05/0.89    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.05/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.05/0.89  fof(f103,plain,(
% 3.05/0.89    ( ! [X4,X2,X3] : (~r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X2),X3)),X4) | k3_xboole_0(k6_relat_1(X2),X3) = k7_relat_1(k3_xboole_0(k6_relat_1(X2),X3),X4)) )),
% 3.05/0.89    inference(forward_demodulation,[],[f100,f86])).
% 3.05/0.89  fof(f100,plain,(
% 3.05/0.89    ( ! [X4,X2,X3] : (~r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X2),X3)),X4) | k3_xboole_0(k6_relat_1(X2),X3) = k5_relat_1(k6_relat_1(X4),k3_xboole_0(k6_relat_1(X2),X3))) )),
% 3.05/0.89    inference(resolution,[],[f56,f63])).
% 3.05/0.89  fof(f56,plain,(
% 3.05/0.89    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 3.05/0.89    inference(cnf_transformation,[],[f33])).
% 3.05/0.89  fof(f33,plain,(
% 3.05/0.89    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.05/0.89    inference(flattening,[],[f32])).
% 3.05/0.89  fof(f32,plain,(
% 3.05/0.89    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.05/0.89    inference(ennf_transformation,[],[f14])).
% 3.05/0.89  fof(f14,axiom,(
% 3.05/0.89    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 3.05/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 3.05/0.89  fof(f128,plain,(
% 3.05/0.89    ( ! [X2,X1] : (k6_relat_1(k3_xboole_0(X1,X2)) = k8_relat_1(X1,k6_relat_1(k3_xboole_0(X1,X2)))) )),
% 3.05/0.89    inference(resolution,[],[f98,f44])).
% 3.05/0.89  fof(f81,plain,(
% 3.05/0.89    k6_relat_1(k3_xboole_0(sK0,sK1)) != k8_relat_1(sK0,k6_relat_1(sK1))),
% 3.05/0.89    inference(backward_demodulation,[],[f38,f79])).
% 3.05/0.89  fof(f38,plain,(
% 3.05/0.89    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.05/0.89    inference(cnf_transformation,[],[f35])).
% 3.05/0.89  fof(f35,plain,(
% 3.05/0.89    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.05/0.89    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f22,f34])).
% 3.05/0.89  fof(f34,plain,(
% 3.05/0.89    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 3.05/0.89    introduced(choice_axiom,[])).
% 3.05/0.89  fof(f22,plain,(
% 3.05/0.89    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 3.05/0.89    inference(ennf_transformation,[],[f20])).
% 3.05/0.89  fof(f20,negated_conjecture,(
% 3.05/0.89    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.05/0.89    inference(negated_conjecture,[],[f19])).
% 3.05/0.89  fof(f19,conjecture,(
% 3.05/0.89    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 3.05/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 3.05/0.89  % SZS output end Proof for theBenchmark
% 3.05/0.89  % (16718)------------------------------
% 3.05/0.89  % (16718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.89  % (16718)Termination reason: Refutation
% 3.05/0.89  
% 3.05/0.89  % (16718)Memory used [KB]: 5373
% 3.05/0.89  % (16718)Time elapsed: 0.418 s
% 3.05/0.89  % (16718)------------------------------
% 3.05/0.89  % (16718)------------------------------
% 3.05/0.89  % (16710)Success in time 0.517 s
%------------------------------------------------------------------------------

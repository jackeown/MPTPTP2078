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
% DateTime   : Thu Dec  3 12:52:26 EST 2020

% Result     : Theorem 11.56s
% Output     : Refutation 11.56s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 175 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :   14
%              Number of atoms          :  168 ( 298 expanded)
%              Number of equality atoms :   74 ( 122 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15738,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f15737])).

fof(f15737,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f162,f15370])).

fof(f15370,plain,(
    ! [X0,X1] : k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1) ),
    inference(forward_demodulation,[],[f15349,f175])).

fof(f175,plain,(
    ! [X2,X1] : k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X1,X2)) ),
    inference(resolution,[],[f98,f52])).

fof(f52,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0) ) ),
    inference(forward_demodulation,[],[f97,f82])).

fof(f82,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0) ),
    inference(resolution,[],[f56,f57])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(forward_demodulation,[],[f94,f49])).

fof(f49,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k6_relat_1(X0)),X1)
      | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) ) ),
    inference(resolution,[],[f44,f57])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k5_relat_1(X1,k6_relat_1(X0)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

fof(f15349,plain,(
    ! [X0,X1] : k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f1790,f2159])).

fof(f2159,plain,(
    ! [X8,X9] : k7_relat_1(k6_relat_1(X9),X8) = k7_relat_1(k7_relat_1(k6_relat_1(X9),X8),k3_xboole_0(X9,X8)) ),
    inference(forward_demodulation,[],[f2140,f88])).

fof(f88,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    inference(forward_demodulation,[],[f85,f48])).

fof(f48,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f85,plain,(
    ! [X0,X1] : k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1) ),
    inference(resolution,[],[f50,f57])).

fof(f50,plain,(
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

fof(f2140,plain,(
    ! [X8,X9] : k7_relat_1(k6_relat_1(X9),X8) = k7_relat_1(k7_relat_1(k6_relat_1(X9),X8),k1_relat_1(k7_relat_1(k6_relat_1(X9),X8))) ),
    inference(superposition,[],[f664,f396])).

fof(f396,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X2),X3) = k3_xboole_0(k6_relat_1(X3),k7_relat_1(k6_relat_1(X2),X3)) ),
    inference(superposition,[],[f120,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f120,plain,(
    ! [X2,X3] : k7_relat_1(k6_relat_1(X3),X2) = k3_xboole_0(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f117,f82])).

fof(f117,plain,(
    ! [X2,X3] : k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)) = k3_xboole_0(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)),k6_relat_1(X2)) ),
    inference(resolution,[],[f69,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f69,plain,(
    ! [X0,X1] : r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0)) ),
    inference(resolution,[],[f54,f57])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f664,plain,(
    ! [X0,X1] : k3_xboole_0(k6_relat_1(X0),X1) = k7_relat_1(k3_xboole_0(k6_relat_1(X0),X1),k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1))) ),
    inference(resolution,[],[f250,f58])).

fof(f58,plain,(
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

fof(f250,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)),X2)
      | k3_xboole_0(k6_relat_1(X0),X1) = k7_relat_1(k3_xboole_0(k6_relat_1(X0),X1),X2) ) ),
    inference(forward_demodulation,[],[f246,f217])).

fof(f217,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k3_xboole_0(k6_relat_1(X1),X2)) = k7_relat_1(k3_xboole_0(k6_relat_1(X1),X2),X0) ),
    inference(resolution,[],[f83,f57])).

fof(f83,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X3)
      | k5_relat_1(k6_relat_1(X2),k3_xboole_0(X3,X4)) = k7_relat_1(k3_xboole_0(X3,X4),X2) ) ),
    inference(resolution,[],[f56,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f246,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X2),k3_xboole_0(k6_relat_1(X0),X1))
      | ~ r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)),X2) ) ),
    inference(resolution,[],[f90,f57])).

fof(f90,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_relat_1(X2)
      | k3_xboole_0(X2,X3) = k5_relat_1(k6_relat_1(X4),k3_xboole_0(X2,X3))
      | ~ r1_tarski(k1_relat_1(k3_xboole_0(X2,X3)),X4) ) ),
    inference(resolution,[],[f43,f51])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f1790,plain,(
    ! [X12,X13,X11] : k7_relat_1(k7_relat_1(k6_relat_1(X13),X11),k3_xboole_0(X12,X11)) = k7_relat_1(k6_relat_1(X13),k3_xboole_0(X12,X11)) ),
    inference(forward_demodulation,[],[f1774,f82])).

fof(f1774,plain,(
    ! [X12,X13,X11] : k7_relat_1(k7_relat_1(k6_relat_1(X13),X11),k3_xboole_0(X12,X11)) = k5_relat_1(k6_relat_1(k3_xboole_0(X12,X11)),k6_relat_1(X13)) ),
    inference(superposition,[],[f632,f176])).

fof(f176,plain,(
    ! [X4,X3] : k6_relat_1(k3_xboole_0(X3,X4)) = k7_relat_1(k6_relat_1(X4),k3_xboole_0(X3,X4)) ),
    inference(resolution,[],[f98,f61])).

fof(f61,plain,(
    ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    inference(superposition,[],[f52,f45])).

fof(f632,plain,(
    ! [X2,X0,X1] : k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f631,f626])).

fof(f626,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) ),
    inference(forward_demodulation,[],[f622,f82])).

fof(f622,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X0) ),
    inference(resolution,[],[f229,f57])).

fof(f229,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k6_relat_1(X0),k5_relat_1(X1,k6_relat_1(X2))) = k7_relat_1(k5_relat_1(X1,k6_relat_1(X2)),X0) ) ),
    inference(resolution,[],[f84,f57])).

fof(f84,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_relat_1(X7)
      | k5_relat_1(k6_relat_1(X5),k5_relat_1(X6,X7)) = k7_relat_1(k5_relat_1(X6,X7),X5)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f56,f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

fof(f631,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2)) ),
    inference(forward_demodulation,[],[f627,f82])).

fof(f627,plain,(
    ! [X2,X0,X1] : k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2)) ),
    inference(resolution,[],[f245,f57])).

fof(f245,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1)) ) ),
    inference(forward_demodulation,[],[f241,f82])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f102,f57])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2)))
      | ~ v1_relat_1(X0) ) ),
    inference(resolution,[],[f46,f57])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f162,plain,(
    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1) ),
    inference(superposition,[],[f38,f82])).

fof(f38,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f34])).

fof(f34,plain,
    ( ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))
   => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:34:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (11117)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (11114)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (11112)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (11116)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (11118)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (11134)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (11126)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (11126)Refutation not found, incomplete strategy% (11126)------------------------------
% 0.21/0.52  % (11126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11128)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (11124)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (11115)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (11113)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (11113)Refutation not found, incomplete strategy% (11113)------------------------------
% 0.21/0.54  % (11113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11127)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (11113)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11113)Memory used [KB]: 1663
% 0.21/0.54  % (11113)Time elapsed: 0.106 s
% 0.21/0.54  % (11113)------------------------------
% 0.21/0.54  % (11113)------------------------------
% 0.21/0.54  % (11135)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (11126)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11126)Memory used [KB]: 1663
% 0.21/0.54  % (11126)Time elapsed: 0.117 s
% 0.21/0.54  % (11126)------------------------------
% 0.21/0.54  % (11126)------------------------------
% 0.21/0.54  % (11136)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (11136)Refutation not found, incomplete strategy% (11136)------------------------------
% 0.21/0.54  % (11136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11136)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11136)Memory used [KB]: 10618
% 0.21/0.54  % (11136)Time elapsed: 0.130 s
% 0.21/0.54  % (11136)------------------------------
% 0.21/0.54  % (11136)------------------------------
% 0.21/0.54  % (11131)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (11128)Refutation not found, incomplete strategy% (11128)------------------------------
% 0.21/0.54  % (11128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11128)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11128)Memory used [KB]: 10618
% 0.21/0.54  % (11128)Time elapsed: 0.134 s
% 0.21/0.54  % (11128)------------------------------
% 0.21/0.54  % (11128)------------------------------
% 0.21/0.54  % (11124)Refutation not found, incomplete strategy% (11124)------------------------------
% 0.21/0.54  % (11124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11124)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11124)Memory used [KB]: 10618
% 0.21/0.54  % (11124)Time elapsed: 0.144 s
% 0.21/0.54  % (11124)------------------------------
% 0.21/0.54  % (11124)------------------------------
% 0.21/0.54  % (11129)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (11140)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (11129)Refutation not found, incomplete strategy% (11129)------------------------------
% 0.21/0.54  % (11129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (11129)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (11129)Memory used [KB]: 1663
% 0.21/0.54  % (11129)Time elapsed: 0.139 s
% 0.21/0.54  % (11129)------------------------------
% 0.21/0.54  % (11129)------------------------------
% 0.21/0.55  % (11141)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (11140)Refutation not found, incomplete strategy% (11140)------------------------------
% 0.21/0.55  % (11140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11140)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11141)Refutation not found, incomplete strategy% (11141)------------------------------
% 0.21/0.55  % (11141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11140)Memory used [KB]: 10746
% 0.21/0.55  % (11140)Time elapsed: 0.140 s
% 0.21/0.55  % (11141)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  % (11140)------------------------------
% 0.21/0.55  % (11140)------------------------------
% 0.21/0.55  
% 0.21/0.55  % (11141)Memory used [KB]: 1663
% 0.21/0.55  % (11141)Time elapsed: 0.139 s
% 0.21/0.55  % (11141)------------------------------
% 0.21/0.55  % (11141)------------------------------
% 0.21/0.55  % (11139)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (11119)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (11139)Refutation not found, incomplete strategy% (11139)------------------------------
% 0.21/0.55  % (11139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11139)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11139)Memory used [KB]: 6140
% 0.21/0.55  % (11139)Time elapsed: 0.126 s
% 0.21/0.55  % (11139)------------------------------
% 0.21/0.55  % (11139)------------------------------
% 0.21/0.55  % (11137)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (11133)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (11132)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (11137)Refutation not found, incomplete strategy% (11137)------------------------------
% 0.21/0.55  % (11137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (11137)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (11137)Memory used [KB]: 6140
% 0.21/0.55  % (11137)Time elapsed: 0.141 s
% 0.21/0.55  % (11137)------------------------------
% 0.21/0.55  % (11137)------------------------------
% 0.21/0.55  % (11125)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.53/0.55  % (11121)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.53/0.55  % (11138)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.53/0.55  % (11122)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.53/0.55  % (11123)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.53/0.55  % (11138)Refutation not found, incomplete strategy% (11138)------------------------------
% 1.53/0.55  % (11138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.55  % (11138)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.55  
% 1.53/0.55  % (11138)Memory used [KB]: 6140
% 1.53/0.55  % (11138)Time elapsed: 0.150 s
% 1.53/0.55  % (11138)------------------------------
% 1.53/0.55  % (11138)------------------------------
% 1.53/0.56  % (11123)Refutation not found, incomplete strategy% (11123)------------------------------
% 1.53/0.56  % (11123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (11123)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (11123)Memory used [KB]: 6140
% 1.53/0.56  % (11123)Time elapsed: 0.150 s
% 1.53/0.56  % (11123)------------------------------
% 1.53/0.56  % (11123)------------------------------
% 1.53/0.56  % (11122)Refutation not found, incomplete strategy% (11122)------------------------------
% 1.53/0.56  % (11122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (11122)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (11122)Memory used [KB]: 10618
% 1.53/0.56  % (11122)Time elapsed: 0.151 s
% 1.53/0.56  % (11122)------------------------------
% 1.53/0.56  % (11122)------------------------------
% 1.53/0.56  % (11130)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.53/0.56  % (11130)Refutation not found, incomplete strategy% (11130)------------------------------
% 1.53/0.56  % (11130)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (11130)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (11130)Memory used [KB]: 1663
% 1.53/0.56  % (11130)Time elapsed: 0.152 s
% 1.53/0.56  % (11130)------------------------------
% 1.53/0.56  % (11130)------------------------------
% 1.53/0.56  % (11120)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 2.10/0.67  % (11145)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.10/0.69  % (11114)Refutation not found, incomplete strategy% (11114)------------------------------
% 2.10/0.69  % (11114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.69  % (11114)Termination reason: Refutation not found, incomplete strategy
% 2.10/0.69  
% 2.10/0.69  % (11114)Memory used [KB]: 6140
% 2.10/0.69  % (11114)Time elapsed: 0.288 s
% 2.10/0.69  % (11114)------------------------------
% 2.10/0.69  % (11114)------------------------------
% 2.10/0.72  % (11152)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.10/0.72  % (11151)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.10/0.72  % (11151)Refutation not found, incomplete strategy% (11151)------------------------------
% 2.10/0.72  % (11151)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.72  % (11151)Termination reason: Refutation not found, incomplete strategy
% 2.10/0.72  
% 2.10/0.72  % (11151)Memory used [KB]: 10618
% 2.10/0.72  % (11151)Time elapsed: 0.142 s
% 2.10/0.72  % (11151)------------------------------
% 2.10/0.72  % (11151)------------------------------
% 2.10/0.72  % (11155)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 2.10/0.72  % (11147)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.51/0.73  % (11115)Refutation not found, incomplete strategy% (11115)------------------------------
% 2.51/0.73  % (11115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.51/0.73  % (11115)Termination reason: Refutation not found, incomplete strategy
% 2.51/0.73  
% 2.51/0.73  % (11115)Memory used [KB]: 6140
% 2.51/0.73  % (11115)Time elapsed: 0.298 s
% 2.51/0.73  % (11115)------------------------------
% 2.51/0.73  % (11115)------------------------------
% 2.51/0.73  % (11148)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.51/0.73  % (11156)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 2.51/0.73  % (11148)Refutation not found, incomplete strategy% (11148)------------------------------
% 2.51/0.73  % (11148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.51/0.73  % (11148)Termination reason: Refutation not found, incomplete strategy
% 2.51/0.73  
% 2.51/0.73  % (11148)Memory used [KB]: 10618
% 2.51/0.73  % (11148)Time elapsed: 0.142 s
% 2.51/0.73  % (11148)------------------------------
% 2.51/0.73  % (11148)------------------------------
% 2.51/0.73  % (11156)Refutation not found, incomplete strategy% (11156)------------------------------
% 2.51/0.73  % (11156)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.51/0.73  % (11156)Termination reason: Refutation not found, incomplete strategy
% 2.51/0.73  
% 2.51/0.73  % (11156)Memory used [KB]: 10746
% 2.51/0.73  % (11156)Time elapsed: 0.155 s
% 2.51/0.73  % (11156)------------------------------
% 2.51/0.73  % (11156)------------------------------
% 2.51/0.74  % (11146)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.51/0.76  % (11149)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.51/0.76  % (11149)Refutation not found, incomplete strategy% (11149)------------------------------
% 2.51/0.76  % (11149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.51/0.76  % (11149)Termination reason: Refutation not found, incomplete strategy
% 2.51/0.76  
% 2.51/0.76  % (11149)Memory used [KB]: 10618
% 2.51/0.76  % (11149)Time elapsed: 0.166 s
% 2.51/0.76  % (11149)------------------------------
% 2.51/0.76  % (11149)------------------------------
% 2.51/0.76  % (11120)Refutation not found, incomplete strategy% (11120)------------------------------
% 2.51/0.76  % (11120)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.51/0.76  % (11158)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 2.51/0.76  % (11158)Refutation not found, incomplete strategy% (11158)------------------------------
% 2.51/0.76  % (11158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.51/0.76  % (11158)Termination reason: Refutation not found, incomplete strategy
% 2.51/0.76  
% 2.51/0.76  % (11158)Memory used [KB]: 10618
% 2.51/0.76  % (11158)Time elapsed: 0.115 s
% 2.51/0.76  % (11158)------------------------------
% 2.51/0.76  % (11158)------------------------------
% 2.51/0.76  % (11150)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.51/0.77  % (11150)Refutation not found, incomplete strategy% (11150)------------------------------
% 2.51/0.77  % (11150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.51/0.77  % (11150)Termination reason: Refutation not found, incomplete strategy
% 2.51/0.77  
% 2.51/0.77  % (11150)Memory used [KB]: 1663
% 2.51/0.77  % (11150)Time elapsed: 0.175 s
% 2.51/0.77  % (11150)------------------------------
% 2.51/0.77  % (11150)------------------------------
% 2.51/0.77  % (11120)Termination reason: Refutation not found, incomplete strategy
% 2.51/0.77  
% 2.51/0.77  % (11120)Memory used [KB]: 6268
% 2.51/0.77  % (11120)Time elapsed: 0.356 s
% 2.51/0.77  % (11120)------------------------------
% 2.51/0.77  % (11120)------------------------------
% 2.51/0.77  % (11153)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.96/0.77  % (11157)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 2.96/0.79  % (11127)Refutation not found, incomplete strategy% (11127)------------------------------
% 2.96/0.79  % (11127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.96/0.79  % (11127)Termination reason: Refutation not found, incomplete strategy
% 2.96/0.79  
% 2.96/0.79  % (11127)Memory used [KB]: 6140
% 2.96/0.79  % (11127)Time elapsed: 0.343 s
% 2.96/0.79  % (11127)------------------------------
% 2.96/0.79  % (11127)------------------------------
% 2.96/0.79  % (11154)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 2.96/0.79  % (11154)Refutation not found, incomplete strategy% (11154)------------------------------
% 2.96/0.79  % (11154)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.96/0.79  % (11154)Termination reason: Refutation not found, incomplete strategy
% 2.96/0.79  
% 2.96/0.79  % (11154)Memory used [KB]: 10618
% 2.96/0.79  % (11154)Time elapsed: 0.204 s
% 2.96/0.79  % (11154)------------------------------
% 2.96/0.79  % (11154)------------------------------
% 3.58/0.88  % (11183)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 3.58/0.89  % (11185)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 3.58/0.91  % (11186)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 3.58/0.92  % (11118)Time limit reached!
% 3.58/0.92  % (11118)------------------------------
% 3.58/0.92  % (11118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.58/0.92  % (11118)Termination reason: Time limit
% 3.58/0.92  
% 3.58/0.92  % (11118)Memory used [KB]: 13688
% 3.58/0.92  % (11118)Time elapsed: 0.509 s
% 3.58/0.92  % (11118)------------------------------
% 3.58/0.92  % (11118)------------------------------
% 3.86/0.93  % (11184)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 4.01/0.96  % (11187)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 4.01/0.97  % (11153)Refutation not found, incomplete strategy% (11153)------------------------------
% 4.01/0.97  % (11153)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.97  % (11153)Termination reason: Refutation not found, incomplete strategy
% 4.01/0.97  
% 4.01/0.97  % (11153)Memory used [KB]: 6268
% 4.01/0.97  % (11153)Time elapsed: 0.359 s
% 4.01/0.97  % (11153)------------------------------
% 4.01/0.97  % (11153)------------------------------
% 4.01/0.98  % (11188)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 4.01/0.98  % (11188)Refutation not found, incomplete strategy% (11188)------------------------------
% 4.01/0.98  % (11188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.01/0.98  % (11188)Termination reason: Refutation not found, incomplete strategy
% 4.01/0.98  
% 4.01/0.98  % (11188)Memory used [KB]: 1663
% 4.01/0.98  % (11188)Time elapsed: 0.176 s
% 4.01/0.98  % (11188)------------------------------
% 4.01/0.98  % (11188)------------------------------
% 4.01/0.99  % (11189)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 4.52/1.07  % (11183)Refutation not found, incomplete strategy% (11183)------------------------------
% 4.52/1.07  % (11183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/1.07  % (11183)Termination reason: Refutation not found, incomplete strategy
% 4.52/1.07  
% 4.52/1.07  % (11183)Memory used [KB]: 6268
% 4.52/1.07  % (11183)Time elapsed: 0.313 s
% 4.52/1.07  % (11183)------------------------------
% 4.52/1.07  % (11183)------------------------------
% 4.52/1.07  % (11119)Time limit reached!
% 4.52/1.07  % (11119)------------------------------
% 4.52/1.07  % (11119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.52/1.08  % (11119)Termination reason: Time limit
% 4.52/1.08  
% 4.52/1.08  % (11119)Memory used [KB]: 5884
% 4.52/1.08  % (11119)Time elapsed: 0.627 s
% 4.52/1.08  % (11119)------------------------------
% 4.52/1.08  % (11119)------------------------------
% 5.69/1.16  % (11184)Refutation not found, incomplete strategy% (11184)------------------------------
% 5.69/1.16  % (11184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.69/1.16  % (11184)Termination reason: Refutation not found, incomplete strategy
% 5.69/1.16  
% 5.69/1.16  % (11184)Memory used [KB]: 6140
% 5.69/1.16  % (11184)Time elapsed: 0.385 s
% 5.69/1.16  % (11184)------------------------------
% 5.69/1.16  % (11184)------------------------------
% 6.35/1.17  % (11186)Time limit reached!
% 6.35/1.17  % (11186)------------------------------
% 6.35/1.17  % (11186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.35/1.17  % (11186)Termination reason: Time limit
% 6.35/1.17  % (11186)Termination phase: Saturation
% 6.35/1.17  
% 6.35/1.17  % (11186)Memory used [KB]: 8315
% 6.35/1.17  % (11186)Time elapsed: 0.400 s
% 6.35/1.17  % (11186)------------------------------
% 6.35/1.17  % (11186)------------------------------
% 6.58/1.21  % (11189)Time limit reached!
% 6.58/1.21  % (11189)------------------------------
% 6.58/1.21  % (11189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.58/1.21  % (11189)Termination reason: Time limit
% 6.58/1.21  
% 6.58/1.21  % (11189)Memory used [KB]: 6780
% 6.58/1.21  % (11189)Time elapsed: 0.405 s
% 6.58/1.21  % (11189)------------------------------
% 6.58/1.21  % (11189)------------------------------
% 6.90/1.26  % (11185)Time limit reached!
% 6.90/1.26  % (11185)------------------------------
% 6.90/1.26  % (11185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.90/1.26  % (11185)Termination reason: Time limit
% 6.90/1.26  
% 6.90/1.26  % (11185)Memory used [KB]: 10490
% 6.90/1.26  % (11185)Time elapsed: 0.519 s
% 6.90/1.26  % (11185)------------------------------
% 6.90/1.26  % (11185)------------------------------
% 7.99/1.41  % (11147)Time limit reached!
% 7.99/1.41  % (11147)------------------------------
% 7.99/1.41  % (11147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.99/1.41  % (11147)Termination reason: Time limit
% 7.99/1.41  % (11147)Termination phase: Saturation
% 7.99/1.41  
% 7.99/1.41  % (11147)Memory used [KB]: 12665
% 7.99/1.41  % (11147)Time elapsed: 0.800 s
% 7.99/1.41  % (11147)------------------------------
% 7.99/1.41  % (11147)------------------------------
% 9.36/1.62  % (11112)Time limit reached!
% 9.36/1.62  % (11112)------------------------------
% 9.36/1.62  % (11112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.36/1.62  % (11112)Termination reason: Time limit
% 9.36/1.62  % (11112)Termination phase: Saturation
% 9.36/1.62  
% 9.36/1.62  % (11112)Memory used [KB]: 19573
% 9.36/1.62  % (11112)Time elapsed: 1.200 s
% 9.36/1.62  % (11112)------------------------------
% 9.36/1.62  % (11112)------------------------------
% 10.59/1.72  % (11117)Time limit reached!
% 10.59/1.72  % (11117)------------------------------
% 10.59/1.72  % (11117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.59/1.72  % (11117)Termination reason: Time limit
% 10.59/1.72  % (11117)Termination phase: Saturation
% 10.59/1.72  
% 10.59/1.72  % (11117)Memory used [KB]: 12665
% 10.59/1.72  % (11117)Time elapsed: 1.300 s
% 10.59/1.72  % (11117)------------------------------
% 10.59/1.72  % (11117)------------------------------
% 11.56/1.89  % (11157)Refutation found. Thanks to Tanya!
% 11.56/1.89  % SZS status Theorem for theBenchmark
% 11.56/1.89  % SZS output start Proof for theBenchmark
% 11.56/1.89  fof(f15738,plain,(
% 11.56/1.89    $false),
% 11.56/1.89    inference(trivial_inequality_removal,[],[f15737])).
% 11.56/1.89  fof(f15737,plain,(
% 11.56/1.89    k6_relat_1(k3_xboole_0(sK0,sK1)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 11.56/1.89    inference(superposition,[],[f162,f15370])).
% 11.56/1.89  fof(f15370,plain,(
% 11.56/1.89    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X0,X1)) = k7_relat_1(k6_relat_1(X0),X1)) )),
% 11.56/1.89    inference(forward_demodulation,[],[f15349,f175])).
% 11.56/1.89  fof(f175,plain,(
% 11.56/1.89    ( ! [X2,X1] : (k6_relat_1(k3_xboole_0(X1,X2)) = k7_relat_1(k6_relat_1(X1),k3_xboole_0(X1,X2))) )),
% 11.56/1.89    inference(resolution,[],[f98,f52])).
% 11.56/1.89  fof(f52,plain,(
% 11.56/1.89    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 11.56/1.89    inference(cnf_transformation,[],[f3])).
% 11.56/1.89  fof(f3,axiom,(
% 11.56/1.89    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 11.56/1.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 11.56/1.89  fof(f98,plain,(
% 11.56/1.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 11.56/1.89    inference(forward_demodulation,[],[f97,f82])).
% 11.56/1.89  fof(f82,plain,(
% 11.56/1.89    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)) = k7_relat_1(k6_relat_1(X1),X0)) )),
% 11.56/1.89    inference(resolution,[],[f56,f57])).
% 11.56/1.89  fof(f57,plain,(
% 11.56/1.89    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 11.56/1.89    inference(cnf_transformation,[],[f8])).
% 11.56/1.89  fof(f8,axiom,(
% 11.56/1.89    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 11.56/1.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 11.56/1.89  fof(f56,plain,(
% 11.56/1.89    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0)) )),
% 11.56/1.89    inference(cnf_transformation,[],[f33])).
% 11.56/1.89  fof(f33,plain,(
% 11.56/1.89    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.56/1.89    inference(ennf_transformation,[],[f17])).
% 11.56/1.89  fof(f17,axiom,(
% 11.56/1.89    ! [X0,X1] : (v1_relat_1(X1) => k5_relat_1(k6_relat_1(X0),X1) = k7_relat_1(X1,X0))),
% 11.56/1.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 11.56/1.89  fof(f97,plain,(
% 11.56/1.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 11.56/1.89    inference(forward_demodulation,[],[f94,f49])).
% 11.56/1.89  fof(f49,plain,(
% 11.56/1.89    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 11.56/1.89    inference(cnf_transformation,[],[f11])).
% 11.56/1.89  fof(f11,axiom,(
% 11.56/1.89    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 11.56/1.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 11.56/1.89  fof(f94,plain,(
% 11.56/1.89    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(k6_relat_1(X0)),X1) | k6_relat_1(X0) = k5_relat_1(k6_relat_1(X0),k6_relat_1(X1))) )),
% 11.56/1.89    inference(resolution,[],[f44,f57])).
% 11.56/1.89  fof(f44,plain,(
% 11.56/1.89    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k2_relat_1(X1),X0) | k5_relat_1(X1,k6_relat_1(X0)) = X1) )),
% 11.56/1.89    inference(cnf_transformation,[],[f25])).
% 11.56/1.89  fof(f25,plain,(
% 11.56/1.89    ! [X0,X1] : (k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 11.56/1.89    inference(flattening,[],[f24])).
% 11.56/1.89  fof(f24,plain,(
% 11.56/1.89    ! [X0,X1] : ((k5_relat_1(X1,k6_relat_1(X0)) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.56/1.89    inference(ennf_transformation,[],[f14])).
% 11.56/1.89  fof(f14,axiom,(
% 11.56/1.89    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k5_relat_1(X1,k6_relat_1(X0)) = X1))),
% 11.56/1.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).
% 11.56/1.89  fof(f15349,plain,(
% 11.56/1.89    ( ! [X0,X1] : (k7_relat_1(k6_relat_1(X0),X1) = k7_relat_1(k6_relat_1(X0),k3_xboole_0(X0,X1))) )),
% 11.56/1.89    inference(superposition,[],[f1790,f2159])).
% 11.56/1.89  fof(f2159,plain,(
% 11.56/1.89    ( ! [X8,X9] : (k7_relat_1(k6_relat_1(X9),X8) = k7_relat_1(k7_relat_1(k6_relat_1(X9),X8),k3_xboole_0(X9,X8))) )),
% 11.56/1.89    inference(forward_demodulation,[],[f2140,f88])).
% 11.56/1.89  fof(f88,plain,(
% 11.56/1.89    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_relat_1(k7_relat_1(k6_relat_1(X0),X1))) )),
% 11.56/1.89    inference(forward_demodulation,[],[f85,f48])).
% 11.56/1.89  fof(f48,plain,(
% 11.56/1.89    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 11.56/1.89    inference(cnf_transformation,[],[f11])).
% 11.56/1.89  fof(f85,plain,(
% 11.56/1.89    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(k6_relat_1(X0),X1)) = k3_xboole_0(k1_relat_1(k6_relat_1(X0)),X1)) )),
% 11.56/1.89    inference(resolution,[],[f50,f57])).
% 11.56/1.89  fof(f50,plain,(
% 11.56/1.89    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 11.56/1.89    inference(cnf_transformation,[],[f28])).
% 11.56/1.89  fof(f28,plain,(
% 11.56/1.89    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 11.56/1.89    inference(ennf_transformation,[],[f16])).
% 11.56/1.89  fof(f16,axiom,(
% 11.56/1.89    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 11.56/1.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).
% 11.56/1.89  fof(f2140,plain,(
% 11.56/1.89    ( ! [X8,X9] : (k7_relat_1(k6_relat_1(X9),X8) = k7_relat_1(k7_relat_1(k6_relat_1(X9),X8),k1_relat_1(k7_relat_1(k6_relat_1(X9),X8)))) )),
% 11.56/1.89    inference(superposition,[],[f664,f396])).
% 11.56/1.89  fof(f396,plain,(
% 11.56/1.89    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X2),X3) = k3_xboole_0(k6_relat_1(X3),k7_relat_1(k6_relat_1(X2),X3))) )),
% 11.56/1.89    inference(superposition,[],[f120,f45])).
% 11.56/1.89  fof(f45,plain,(
% 11.56/1.89    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 11.56/1.89    inference(cnf_transformation,[],[f1])).
% 11.56/1.89  fof(f1,axiom,(
% 11.56/1.89    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 11.56/1.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 11.56/1.89  fof(f120,plain,(
% 11.56/1.89    ( ! [X2,X3] : (k7_relat_1(k6_relat_1(X3),X2) = k3_xboole_0(k7_relat_1(k6_relat_1(X3),X2),k6_relat_1(X2))) )),
% 11.56/1.89    inference(forward_demodulation,[],[f117,f82])).
% 11.56/1.89  fof(f117,plain,(
% 11.56/1.89    ( ! [X2,X3] : (k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)) = k3_xboole_0(k5_relat_1(k6_relat_1(X2),k6_relat_1(X3)),k6_relat_1(X2))) )),
% 11.56/1.89    inference(resolution,[],[f69,f42])).
% 11.56/1.89  fof(f42,plain,(
% 11.56/1.89    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 11.56/1.89    inference(cnf_transformation,[],[f21])).
% 11.56/1.89  fof(f21,plain,(
% 11.56/1.89    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 11.56/1.89    inference(ennf_transformation,[],[f4])).
% 11.56/1.89  fof(f4,axiom,(
% 11.56/1.89    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 11.56/1.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 11.56/1.89  fof(f69,plain,(
% 11.56/1.89    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X0))) )),
% 11.56/1.89    inference(resolution,[],[f54,f57])).
% 11.56/1.89  fof(f54,plain,(
% 11.56/1.89    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) )),
% 11.56/1.89    inference(cnf_transformation,[],[f32])).
% 11.56/1.89  fof(f32,plain,(
% 11.56/1.89    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 11.56/1.89    inference(ennf_transformation,[],[f12])).
% 11.56/1.89  fof(f12,axiom,(
% 11.56/1.89    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 11.56/1.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 11.56/1.89  fof(f664,plain,(
% 11.56/1.89    ( ! [X0,X1] : (k3_xboole_0(k6_relat_1(X0),X1) = k7_relat_1(k3_xboole_0(k6_relat_1(X0),X1),k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)))) )),
% 11.56/1.89    inference(resolution,[],[f250,f58])).
% 11.56/1.89  fof(f58,plain,(
% 11.56/1.89    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.56/1.89    inference(equality_resolution,[],[f40])).
% 11.56/1.89  fof(f40,plain,(
% 11.56/1.89    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.56/1.89    inference(cnf_transformation,[],[f37])).
% 11.56/1.89  fof(f37,plain,(
% 11.56/1.89    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.56/1.89    inference(flattening,[],[f36])).
% 11.56/1.89  fof(f36,plain,(
% 11.56/1.89    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.56/1.89    inference(nnf_transformation,[],[f2])).
% 11.56/1.89  fof(f2,axiom,(
% 11.56/1.89    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.56/1.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 11.56/1.89  fof(f250,plain,(
% 11.56/1.89    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)),X2) | k3_xboole_0(k6_relat_1(X0),X1) = k7_relat_1(k3_xboole_0(k6_relat_1(X0),X1),X2)) )),
% 11.56/1.89    inference(forward_demodulation,[],[f246,f217])).
% 11.56/1.89  fof(f217,plain,(
% 11.56/1.89    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k3_xboole_0(k6_relat_1(X1),X2)) = k7_relat_1(k3_xboole_0(k6_relat_1(X1),X2),X0)) )),
% 11.56/1.89    inference(resolution,[],[f83,f57])).
% 11.56/1.89  fof(f83,plain,(
% 11.56/1.89    ( ! [X4,X2,X3] : (~v1_relat_1(X3) | k5_relat_1(k6_relat_1(X2),k3_xboole_0(X3,X4)) = k7_relat_1(k3_xboole_0(X3,X4),X2)) )),
% 11.56/1.89    inference(resolution,[],[f56,f51])).
% 11.56/1.89  fof(f51,plain,(
% 11.56/1.89    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 11.56/1.89    inference(cnf_transformation,[],[f29])).
% 11.56/1.89  fof(f29,plain,(
% 11.56/1.89    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 11.56/1.89    inference(ennf_transformation,[],[f9])).
% 11.56/1.89  fof(f9,axiom,(
% 11.56/1.89    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 11.56/1.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 11.56/1.89  fof(f246,plain,(
% 11.56/1.89    ( ! [X2,X0,X1] : (k3_xboole_0(k6_relat_1(X0),X1) = k5_relat_1(k6_relat_1(X2),k3_xboole_0(k6_relat_1(X0),X1)) | ~r1_tarski(k1_relat_1(k3_xboole_0(k6_relat_1(X0),X1)),X2)) )),
% 11.56/1.89    inference(resolution,[],[f90,f57])).
% 11.56/1.90  fof(f90,plain,(
% 11.56/1.90    ( ! [X4,X2,X3] : (~v1_relat_1(X2) | k3_xboole_0(X2,X3) = k5_relat_1(k6_relat_1(X4),k3_xboole_0(X2,X3)) | ~r1_tarski(k1_relat_1(k3_xboole_0(X2,X3)),X4)) )),
% 11.56/1.90    inference(resolution,[],[f43,f51])).
% 11.56/1.90  fof(f43,plain,(
% 11.56/1.90    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(k1_relat_1(X1),X0) | k5_relat_1(k6_relat_1(X0),X1) = X1) )),
% 11.56/1.90    inference(cnf_transformation,[],[f23])).
% 11.56/1.90  fof(f23,plain,(
% 11.56/1.90    ! [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 11.56/1.90    inference(flattening,[],[f22])).
% 11.56/1.90  fof(f22,plain,(
% 11.56/1.90    ! [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) = X1 | ~r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.56/1.90    inference(ennf_transformation,[],[f13])).
% 11.56/1.90  fof(f13,axiom,(
% 11.56/1.90    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 11.56/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 11.56/1.90  fof(f1790,plain,(
% 11.56/1.90    ( ! [X12,X13,X11] : (k7_relat_1(k7_relat_1(k6_relat_1(X13),X11),k3_xboole_0(X12,X11)) = k7_relat_1(k6_relat_1(X13),k3_xboole_0(X12,X11))) )),
% 11.56/1.90    inference(forward_demodulation,[],[f1774,f82])).
% 11.56/1.90  fof(f1774,plain,(
% 11.56/1.90    ( ! [X12,X13,X11] : (k7_relat_1(k7_relat_1(k6_relat_1(X13),X11),k3_xboole_0(X12,X11)) = k5_relat_1(k6_relat_1(k3_xboole_0(X12,X11)),k6_relat_1(X13))) )),
% 11.56/1.90    inference(superposition,[],[f632,f176])).
% 11.56/1.90  fof(f176,plain,(
% 11.56/1.90    ( ! [X4,X3] : (k6_relat_1(k3_xboole_0(X3,X4)) = k7_relat_1(k6_relat_1(X4),k3_xboole_0(X3,X4))) )),
% 11.56/1.90    inference(resolution,[],[f98,f61])).
% 11.56/1.90  fof(f61,plain,(
% 11.56/1.90    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X3,X2),X2)) )),
% 11.56/1.90    inference(superposition,[],[f52,f45])).
% 11.56/1.90  fof(f632,plain,(
% 11.56/1.90    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 11.56/1.90    inference(forward_demodulation,[],[f631,f626])).
% 11.56/1.90  fof(f626,plain,(
% 11.56/1.90    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k7_relat_1(k7_relat_1(k6_relat_1(X2),X1),X0)) )),
% 11.56/1.90    inference(forward_demodulation,[],[f622,f82])).
% 11.56/1.90  fof(f622,plain,(
% 11.56/1.90    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) = k7_relat_1(k5_relat_1(k6_relat_1(X1),k6_relat_1(X2)),X0)) )),
% 11.56/1.90    inference(resolution,[],[f229,f57])).
% 11.56/1.90  fof(f229,plain,(
% 11.56/1.90    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k6_relat_1(X0),k5_relat_1(X1,k6_relat_1(X2))) = k7_relat_1(k5_relat_1(X1,k6_relat_1(X2)),X0)) )),
% 11.56/1.90    inference(resolution,[],[f84,f57])).
% 11.56/1.90  fof(f84,plain,(
% 11.56/1.90    ( ! [X6,X7,X5] : (~v1_relat_1(X7) | k5_relat_1(k6_relat_1(X5),k5_relat_1(X6,X7)) = k7_relat_1(k5_relat_1(X6,X7),X5) | ~v1_relat_1(X6)) )),
% 11.56/1.90    inference(resolution,[],[f56,f53])).
% 11.56/1.90  fof(f53,plain,(
% 11.56/1.90    ( ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.56/1.90    inference(cnf_transformation,[],[f31])).
% 11.56/1.90  fof(f31,plain,(
% 11.56/1.90    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 11.56/1.90    inference(flattening,[],[f30])).
% 11.56/1.90  fof(f30,plain,(
% 11.56/1.90    ! [X0,X1] : (v1_relat_1(k5_relat_1(X0,X1)) | (~v1_relat_1(X1) | ~v1_relat_1(X0)))),
% 11.56/1.90    inference(ennf_transformation,[],[f7])).
% 11.56/1.90  fof(f7,axiom,(
% 11.56/1.90    ! [X0,X1] : ((v1_relat_1(X1) & v1_relat_1(X0)) => v1_relat_1(k5_relat_1(X0,X1)))),
% 11.56/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).
% 11.56/1.90  fof(f631,plain,(
% 11.56/1.90    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k7_relat_1(k6_relat_1(X1),X0),k6_relat_1(X2))) )),
% 11.56/1.90    inference(forward_demodulation,[],[f627,f82])).
% 11.56/1.90  fof(f627,plain,(
% 11.56/1.90    ( ! [X2,X0,X1] : (k5_relat_1(k6_relat_1(X0),k7_relat_1(k6_relat_1(X2),X1)) = k5_relat_1(k5_relat_1(k6_relat_1(X0),k6_relat_1(X1)),k6_relat_1(X2))) )),
% 11.56/1.90    inference(resolution,[],[f245,f57])).
% 11.56/1.90  fof(f245,plain,(
% 11.56/1.90    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k7_relat_1(k6_relat_1(X2),X1))) )),
% 11.56/1.90    inference(forward_demodulation,[],[f241,f82])).
% 11.56/1.90  fof(f241,plain,(
% 11.56/1.90    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,k6_relat_1(X1)),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(k6_relat_1(X1),k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 11.56/1.90    inference(resolution,[],[f102,f57])).
% 11.56/1.90  fof(f102,plain,(
% 11.56/1.90    ( ! [X2,X0,X1] : (~v1_relat_1(X1) | k5_relat_1(k5_relat_1(X0,X1),k6_relat_1(X2)) = k5_relat_1(X0,k5_relat_1(X1,k6_relat_1(X2))) | ~v1_relat_1(X0)) )),
% 11.56/1.90    inference(resolution,[],[f46,f57])).
% 11.56/1.90  fof(f46,plain,(
% 11.56/1.90    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.56/1.90    inference(cnf_transformation,[],[f26])).
% 11.56/1.90  fof(f26,plain,(
% 11.56/1.90    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.56/1.90    inference(ennf_transformation,[],[f10])).
% 11.56/1.90  fof(f10,axiom,(
% 11.56/1.90    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 11.56/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 11.56/1.90  fof(f162,plain,(
% 11.56/1.90    k6_relat_1(k3_xboole_0(sK0,sK1)) != k7_relat_1(k6_relat_1(sK0),sK1)),
% 11.56/1.90    inference(superposition,[],[f38,f82])).
% 11.56/1.90  fof(f38,plain,(
% 11.56/1.90    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 11.56/1.90    inference(cnf_transformation,[],[f35])).
% 11.56/1.90  fof(f35,plain,(
% 11.56/1.90    k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 11.56/1.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f34])).
% 11.56/1.90  fof(f34,plain,(
% 11.56/1.90    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1)) => k5_relat_1(k6_relat_1(sK1),k6_relat_1(sK0)) != k6_relat_1(k3_xboole_0(sK0,sK1))),
% 11.56/1.90    introduced(choice_axiom,[])).
% 11.56/1.90  fof(f20,plain,(
% 11.56/1.90    ? [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) != k6_relat_1(k3_xboole_0(X0,X1))),
% 11.56/1.90    inference(ennf_transformation,[],[f19])).
% 11.56/1.90  fof(f19,negated_conjecture,(
% 11.56/1.90    ~! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 11.56/1.90    inference(negated_conjecture,[],[f18])).
% 11.56/1.90  fof(f18,conjecture,(
% 11.56/1.90    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 11.56/1.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).
% 11.56/1.90  % SZS output end Proof for theBenchmark
% 11.56/1.90  % (11157)------------------------------
% 11.56/1.90  % (11157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.56/1.90  % (11157)Termination reason: Refutation
% 11.56/1.90  
% 11.56/1.90  % (11157)Memory used [KB]: 18293
% 11.56/1.90  % (11157)Time elapsed: 1.273 s
% 11.56/1.90  % (11157)------------------------------
% 11.56/1.90  % (11157)------------------------------
% 11.56/1.90  % (11111)Success in time 1.531 s
%------------------------------------------------------------------------------

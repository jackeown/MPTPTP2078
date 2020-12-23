%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:48 EST 2020

% Result     : Theorem 4.69s
% Output     : Refutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :  374 (24596091 expanded)
%              Number of leaves         :   10 (7747552 expanded)
%              Depth                    :  103
%              Number of atoms          :  384 (31317651 expanded)
%              Number of equality atoms :  355 (20539810 expanded)
%              Maximal formula depth    :    7 (   2 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7937,plain,(
    $false ),
    inference(subsumption_resolution,[],[f16,f7892])).

fof(f7892,plain,(
    ! [X2] : r1_tarski(k3_xboole_0(sK0,X2),sK1) ),
    inference(superposition,[],[f6576,f7828])).

fof(f7828,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0) ),
    inference(backward_demodulation,[],[f6756,f7760])).

fof(f7760,plain,(
    ! [X16] : k3_xboole_0(sK0,X16) = k4_xboole_0(sK0,k4_xboole_0(sK0,X16)) ),
    inference(backward_demodulation,[],[f6739,f7758])).

fof(f7758,plain,(
    ! [X10] : k3_xboole_0(sK0,X10) = k5_xboole_0(sK0,k4_xboole_0(sK0,X10)) ),
    inference(forward_demodulation,[],[f7739,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f7739,plain,(
    ! [X10] : k3_xboole_0(sK0,X10) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X10))) ),
    inference(superposition,[],[f5771,f62])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f24,f21])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f24,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f5771,plain,(
    ! [X0] : k5_xboole_0(sK0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,X0))) ),
    inference(backward_demodulation,[],[f5332,f5498])).

fof(f5498,plain,(
    ! [X1] : k5_xboole_0(sK1,k5_xboole_0(sK1,X1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,X1)) ),
    inference(backward_demodulation,[],[f4671,f5331])).

fof(f5331,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f5330,f1756])).

fof(f1756,plain,(
    sK0 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    inference(superposition,[],[f30,f1693])).

fof(f1693,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f1688,f20])).

fof(f1688,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f111,f1683])).

fof(f1683,plain,(
    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1682,f63])).

fof(f63,plain,(
    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f24,f44])).

fof(f44,plain,(
    k3_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f21,f29])).

fof(f29,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f22,f15])).

fof(f15,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k3_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k3_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1682,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1679,f29])).

fof(f1679,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f55,f1668])).

fof(f1668,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1667,f29])).

fof(f1667,plain,(
    k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k5_xboole_0(k2_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f1661,f55])).

fof(f1661,plain,(
    k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),sK1)) ),
    inference(superposition,[],[f1149,f1654])).

fof(f1654,plain,(
    sK1 = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f1651,f77])).

fof(f77,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(sK0,sK1),X0) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f75,f24])).

fof(f75,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(sK0,sK1),X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,sK1),X0)) ),
    inference(superposition,[],[f24,f63])).

fof(f1651,plain,(
    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(backward_demodulation,[],[f1650,f1646])).

fof(f1646,plain,(
    k5_xboole_0(sK1,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f55,f1352])).

fof(f1352,plain,(
    k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f1166,f1339])).

fof(f1339,plain,(
    k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f1126,f1310])).

fof(f1310,plain,(
    ! [X26,X25] : k5_xboole_0(k4_xboole_0(sK1,X25),k3_xboole_0(k3_xboole_0(X25,sK1),X26)) = k4_xboole_0(sK1,k4_xboole_0(X25,X26)) ),
    inference(forward_demodulation,[],[f1309,f1128])).

fof(f1128,plain,(
    ! [X2,X3] : k4_xboole_0(sK1,k4_xboole_0(X2,X3)) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(X2,k4_xboole_0(sK1,X3)))) ),
    inference(superposition,[],[f1118,f130])).

fof(f130,plain,(
    ! [X4,X5,X3] : k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5)) ),
    inference(superposition,[],[f52,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2) ),
    inference(superposition,[],[f23,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f1118,plain,(
    ! [X1] : k4_xboole_0(sK1,X1) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,X1))) ),
    inference(superposition,[],[f1083,f162])).

fof(f162,plain,(
    ! [X0,X1] : k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,X0),X1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(sK1,X0),X1))) ),
    inference(forward_demodulation,[],[f161,f24])).

fof(f161,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(sK1,X0)),X1)) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,X0),X1)) ),
    inference(forward_demodulation,[],[f159,f24])).

fof(f159,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(sK1,X0)),X1)) = k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,X0)),X1) ),
    inference(superposition,[],[f24,f152])).

fof(f152,plain,(
    ! [X8] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(X8,k2_xboole_0(sK1,X8))) = k5_xboole_0(sK0,k4_xboole_0(sK1,X8)) ),
    inference(forward_demodulation,[],[f145,f20])).

fof(f145,plain,(
    ! [X8] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(X8,k2_xboole_0(sK1,X8))) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X8))) ),
    inference(superposition,[],[f77,f62])).

fof(f1083,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,X0)))) ),
    inference(forward_demodulation,[],[f1082,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f20,f18])).

fof(f1082,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,X0)))) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1)) ),
    inference(forward_demodulation,[],[f1081,f29])).

fof(f1081,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,X0)))) = k5_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(X0,sK1)) ),
    inference(forward_demodulation,[],[f1074,f55])).

fof(f1074,plain,(
    ! [X0] : k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(X0,sK1))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,X0)))) ),
    inference(superposition,[],[f162,f1055])).

fof(f1055,plain,(
    ! [X1] : k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(X1,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,X1)) ),
    inference(superposition,[],[f973,f55])).

fof(f973,plain,(
    ! [X1] : k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(X1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK1,X1))) ),
    inference(superposition,[],[f55,f958])).

fof(f958,plain,(
    ! [X1] : k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(X1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK1,X1)) ),
    inference(superposition,[],[f833,f832])).

fof(f832,plain,(
    ! [X0] : k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK1,X0)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,X0)))) ),
    inference(superposition,[],[f56,f86])).

fof(f86,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,X1))) ),
    inference(forward_demodulation,[],[f79,f24])).

fof(f79,plain,(
    ! [X1] : k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK1,X1)) ),
    inference(superposition,[],[f59,f20])).

fof(f59,plain,(
    ! [X12] : k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,X12)) = k5_xboole_0(k3_xboole_0(sK0,sK1),X12) ),
    inference(superposition,[],[f24,f44])).

fof(f56,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X4),X5)) = k5_xboole_0(k4_xboole_0(X3,X4),X5) ),
    inference(superposition,[],[f24,f20])).

fof(f833,plain,(
    ! [X1] : k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(X1,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,X1)))) ),
    inference(superposition,[],[f56,f87])).

fof(f87,plain,(
    ! [X2] : k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X2,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,X2))) ),
    inference(forward_demodulation,[],[f80,f24])).

fof(f80,plain,(
    ! [X2] : k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X2,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK1,X2)) ),
    inference(superposition,[],[f59,f36])).

fof(f1309,plain,(
    ! [X26,X25] : k5_xboole_0(k4_xboole_0(sK1,X25),k3_xboole_0(k3_xboole_0(X25,sK1),X26)) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(X25,k4_xboole_0(sK1,X26)))) ),
    inference(forward_demodulation,[],[f1280,f23])).

fof(f1280,plain,(
    ! [X26,X25] : k5_xboole_0(k4_xboole_0(sK1,X25),k3_xboole_0(k3_xboole_0(X25,sK1),X26)) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k3_xboole_0(X25,sK1),X26))) ),
    inference(superposition,[],[f1149,f20])).

fof(f1126,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(X0,sK1))) ),
    inference(superposition,[],[f1118,f18])).

fof(f1166,plain,(
    k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k5_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f56,f1093])).

fof(f1093,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1092,f659])).

fof(f659,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f633,f18])).

fof(f633,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(superposition,[],[f54,f20])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k3_xboole_0(X0,X1)) = k5_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f19,f23])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f1092,plain,(
    k2_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1091,f54])).

fof(f1091,plain,(
    k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k5_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f1090,f29])).

fof(f1090,plain,(
    k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k5_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f1087,f55])).

fof(f1087,plain,(
    k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f162,f1067])).

fof(f1067,plain,(
    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK0,k4_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f1066,f130])).

fof(f1066,plain,(
    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1065,f18])).

fof(f1065,plain,(
    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f1053,f19])).

fof(f1053,plain,(
    k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) ),
    inference(superposition,[],[f973,f36])).

fof(f1650,plain,(
    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))))) ),
    inference(forward_demodulation,[],[f1649,f31])).

fof(f31,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(X2,X3),X3) = X3 ),
    inference(resolution,[],[f22,f25])).

fof(f25,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f17,f18])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f1649,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))))) = k2_xboole_0(k3_xboole_0(sK0,sK1),sK1) ),
    inference(forward_demodulation,[],[f1645,f19])).

fof(f1645,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f104,f1352])).

fof(f104,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(X0,sK1),X1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK1,X0),X1))) ),
    inference(forward_demodulation,[],[f103,f24])).

fof(f103,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(X0,sK1),X1)) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK1,X0)),X1)) ),
    inference(forward_demodulation,[],[f101,f24])).

fof(f101,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(X0,sK1),X1)) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,X0))),X1) ),
    inference(superposition,[],[f24,f85])).

fof(f85,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(X0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,X0))) ),
    inference(forward_demodulation,[],[f78,f24])).

fof(f78,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(X0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f59,f19])).

fof(f1149,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(sK1,X1),X2) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(k3_xboole_0(X1,sK1),X2))) ),
    inference(forward_demodulation,[],[f1145,f24])).

fof(f1145,plain,(
    ! [X2,X1] : k5_xboole_0(k4_xboole_0(sK1,X1),X2) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(X1,sK1)),X2)) ),
    inference(superposition,[],[f24,f1126])).

fof(f55,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(superposition,[],[f24,f19])).

fof(f111,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f107,f23])).

fof(f107,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f86,f36])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f22,f17])).

fof(f5330,plain,(
    k3_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) ),
    inference(forward_demodulation,[],[f5311,f4634])).

fof(f4634,plain,(
    k3_xboole_0(sK0,sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f3850,f4629])).

fof(f4629,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f3845,f4574])).

fof(f4574,plain,(
    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f63,f4573])).

fof(f4573,plain,(
    k5_xboole_0(sK1,sK1) = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f4572,f1693])).

fof(f4572,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f4401,f1748])).

fof(f1748,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f177,f1693])).

fof(f177,plain,(
    ! [X21,X19,X20] : k2_xboole_0(k3_xboole_0(X20,k4_xboole_0(X19,X21)),X19) = X19 ),
    inference(superposition,[],[f30,f130])).

fof(f4401,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)) ),
    inference(backward_demodulation,[],[f1826,f4385])).

fof(f4385,plain,(
    sK1 = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f4384,f2579])).

fof(f2579,plain,(
    sK1 = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f2355,f2576])).

fof(f2576,plain,(
    sK1 = k5_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2575,f29])).

fof(f2575,plain,(
    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2574,f19])).

fof(f2574,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2573,f36])).

fof(f2573,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2563,f2355])).

fof(f2563,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f77,f2509])).

fof(f2509,plain,(
    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f2354,f2505])).

fof(f2505,plain,(
    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2504,f63])).

fof(f2504,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2499,f148])).

fof(f148,plain,(
    ! [X2,X3] : k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X3)) = k3_xboole_0(X3,k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f136,f18])).

fof(f136,plain,(
    ! [X2,X3] : k3_xboole_0(k3_xboole_0(X2,X3),X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X3)) ),
    inference(superposition,[],[f62,f31])).

fof(f2499,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f77,f2494])).

fof(f2494,plain,(
    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f2489,f29])).

fof(f2489,plain,(
    sK1 = k5_xboole_0(k2_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f2133,f55])).

fof(f2133,plain,(
    sK1 = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f2132,f29])).

fof(f2132,plain,(
    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f2131,f19])).

fof(f2131,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f2128,f152])).

fof(f2128,plain,(
    k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[],[f162,f2007])).

fof(f2007,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f2002,f19])).

fof(f2002,plain,(
    k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f55,f1795])).

fof(f1795,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f1794,f1693])).

fof(f1794,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f1793,f130])).

fof(f1793,plain,(
    k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f1789,f18])).

fof(f1789,plain,(
    k3_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f62,f1748])).

fof(f2354,plain,(
    k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f1813,f2353])).

fof(f2353,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2352,f36])).

fof(f2352,plain,(
    k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2351,f18])).

fof(f2351,plain,(
    k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2350,f63])).

fof(f2350,plain,(
    k5_xboole_0(k3_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f2265,f24])).

fof(f2265,plain,(
    k5_xboole_0(k3_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k5_xboole_0(k5_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f58,f1965])).

fof(f1965,plain,(
    k5_xboole_0(sK1,sK1) = k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f55,f1925])).

fof(f1925,plain,(
    sK1 = k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f1878,f1748])).

fof(f1878,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f19,f1806])).

fof(f1806,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK0) ),
    inference(superposition,[],[f1775,f659])).

fof(f1775,plain,(
    k2_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f1745,f19])).

fof(f1745,plain,(
    k2_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f54,f1693])).

fof(f58,plain,(
    ! [X10,X11,X9] : k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(k2_xboole_0(X9,X10),X11)) = k5_xboole_0(k3_xboole_0(X9,X10),X11) ),
    inference(superposition,[],[f24,f21])).

fof(f1813,plain,(
    k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[],[f62,f1775])).

fof(f2355,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f1810,f2353])).

fof(f1810,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0))) ),
    inference(superposition,[],[f152,f1775])).

fof(f4384,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f4363,f2698])).

fof(f2698,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f1821,f2679])).

fof(f2679,plain,(
    k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK0) ),
    inference(forward_demodulation,[],[f2637,f1086])).

fof(f1086,plain,(
    ! [X0] : k4_xboole_0(sK1,X0) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(X0,sK1)))) ),
    inference(forward_demodulation,[],[f1085,f20])).

fof(f1085,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(X0,sK1)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f1084,f29])).

fof(f1084,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(X0,sK1)))) = k5_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f1078,f55])).

fof(f1078,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(X0,sK1)))) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,X0))) ),
    inference(superposition,[],[f162,f1055])).

fof(f2637,plain,(
    k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f1083,f2505])).

fof(f1821,plain,(
    k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k2_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f1339,f1806])).

fof(f4363,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f2978,f4358])).

fof(f4358,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k3_xboole_0(sK0,sK0)) ),
    inference(forward_demodulation,[],[f4341,f1806])).

fof(f4341,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k3_xboole_0(sK0,sK0)) ),
    inference(backward_demodulation,[],[f3207,f4316])).

fof(f4316,plain,(
    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4314,f1795])).

fof(f4314,plain,(
    k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f4313,f4294])).

fof(f4294,plain,(
    k5_xboole_0(sK1,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f31,f3962])).

fof(f3962,plain,(
    k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK0,sK1) ),
    inference(forward_demodulation,[],[f3961,f2756])).

fof(f2756,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2755,f1693])).

fof(f2755,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2655,f23])).

fof(f2655,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f36,f2505])).

fof(f3961,plain,(
    k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3960,f3940])).

fof(f3940,plain,(
    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f3939,f63])).

fof(f3939,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f3913,f633])).

fof(f3913,plain,(
    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f54,f3900])).

fof(f3900,plain,(
    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f3899,f1965])).

fof(f3899,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f3898,f2750])).

fof(f2750,plain,(
    ! [X7] : k3_xboole_0(sK0,k4_xboole_0(sK1,X7)) = k3_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK1,X7))) ),
    inference(forward_demodulation,[],[f2651,f23])).

fof(f2651,plain,(
    ! [X7] : k4_xboole_0(k3_xboole_0(sK0,sK1),X7) = k3_xboole_0(sK1,k4_xboole_0(k3_xboole_0(sK0,sK1),X7)) ),
    inference(superposition,[],[f23,f2505])).

fof(f3898,plain,(
    k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k3_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(forward_demodulation,[],[f3897,f23])).

fof(f3897,plain,(
    k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k3_xboole_0(sK1,k4_xboole_0(k3_xboole_0(sK0,sK1),sK0)) ),
    inference(forward_demodulation,[],[f3896,f130])).

fof(f3896,plain,(
    k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k3_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f3895,f18])).

fof(f3895,plain,(
    k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k3_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3876,f3894])).

fof(f3894,plain,(
    k2_xboole_0(sK1,sK0) = k2_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3875,f2748])).

fof(f2748,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2648,f1806])).

fof(f2648,plain,(
    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f1312,f2505])).

fof(f1312,plain,(
    ! [X28,X27] : k5_xboole_0(k4_xboole_0(sK1,X27),k3_xboole_0(X28,k3_xboole_0(X27,sK1))) = k4_xboole_0(sK1,k4_xboole_0(X27,X28)) ),
    inference(forward_demodulation,[],[f1311,f1128])).

fof(f1311,plain,(
    ! [X28,X27] : k5_xboole_0(k4_xboole_0(sK1,X27),k3_xboole_0(X28,k3_xboole_0(X27,sK1))) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(X27,k4_xboole_0(sK1,X28)))) ),
    inference(forward_demodulation,[],[f1281,f23])).

fof(f1281,plain,(
    ! [X28,X27] : k5_xboole_0(k4_xboole_0(sK1,X27),k3_xboole_0(X28,k3_xboole_0(X27,sK1))) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k3_xboole_0(X27,sK1),X28))) ),
    inference(superposition,[],[f1149,f36])).

fof(f3875,plain,(
    k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f19,f2774])).

fof(f2774,plain,(
    k3_xboole_0(sK0,sK1) = k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2773,f2679])).

fof(f2773,plain,(
    k3_xboole_0(sK0,sK1) = k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f2663,f2654])).

fof(f2654,plain,(
    k3_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f31,f2505])).

fof(f2663,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f659,f2505])).

fof(f3876,plain,(
    k3_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f40,f2774])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f21,f19])).

fof(f3960,plain,(
    k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(backward_demodulation,[],[f3908,f3959])).

fof(f3959,plain,(
    k4_xboole_0(sK1,sK0) = k4_xboole_0(k4_xboole_0(sK1,sK0),sK0) ),
    inference(forward_demodulation,[],[f3926,f3234])).

fof(f3234,plain,(
    k4_xboole_0(sK1,sK0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f3228,f1126])).

fof(f3228,plain,(
    k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f1149,f2363])).

fof(f2363,plain,(
    k3_xboole_0(sK0,sK1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f2362,f18])).

fof(f2362,plain,(
    k3_xboole_0(sK1,sK0) = k5_xboole_0(k3_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f2268,f21])).

fof(f2268,plain,(
    k5_xboole_0(k3_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1)) = k5_xboole_0(k5_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f58,f2007])).

fof(f3926,plain,(
    k4_xboole_0(k4_xboole_0(sK1,sK0),sK0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f36,f3900])).

fof(f3908,plain,(
    k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK0),sK0))) ),
    inference(backward_demodulation,[],[f3835,f3900])).

fof(f3835,plain,(
    k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK0),sK0))) = k3_xboole_0(sK0,k3_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(forward_demodulation,[],[f3834,f130])).

fof(f3834,plain,(
    k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK0),sK0))) = k3_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK0,sK0))) ),
    inference(forward_demodulation,[],[f3833,f3529])).

fof(f3529,plain,(
    ! [X14] : k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,sK0))) = k3_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(X14,sK0))) ),
    inference(forward_demodulation,[],[f3527,f639])).

fof(f639,plain,(
    ! [X6,X8,X7] : k3_xboole_0(X6,k3_xboole_0(X7,k4_xboole_0(X8,X6))) = k5_xboole_0(k2_xboole_0(X6,k3_xboole_0(X7,X8)),k2_xboole_0(X6,k3_xboole_0(X7,k4_xboole_0(X8,X6)))) ),
    inference(superposition,[],[f21,f54])).

fof(f3527,plain,(
    ! [X14] : k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,sK0))) = k5_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,X14)),k2_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(X14,sK0)))) ),
    inference(backward_demodulation,[],[f3506,f3514])).

fof(f3514,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X2,k4_xboole_0(sK1,X3))) = k2_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(X2,X3))) ),
    inference(backward_demodulation,[],[f749,f3496])).

fof(f3496,plain,(
    ! [X1] : k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X1)) = k2_xboole_0(sK0,k3_xboole_0(sK1,X1)) ),
    inference(backward_demodulation,[],[f742,f3494])).

fof(f3494,plain,(
    ! [X15] : k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X15,sK1)) = k2_xboole_0(sK0,k3_xboole_0(sK1,X15)) ),
    inference(forward_demodulation,[],[f3493,f54])).

fof(f3493,plain,(
    ! [X15] : k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X15,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(X15,sK0))) ),
    inference(backward_demodulation,[],[f2827,f3396])).

fof(f3396,plain,(
    ! [X33,X32] : k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X32,k4_xboole_0(sK1,X33))) = k5_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(X32,X33))) ),
    inference(backward_demodulation,[],[f181,f3367])).

fof(f3367,plain,(
    ! [X8] : k3_xboole_0(sK1,X8) = k5_xboole_0(sK1,k4_xboole_0(sK1,X8)) ),
    inference(forward_demodulation,[],[f3350,f20])).

fof(f3350,plain,(
    ! [X8] : k3_xboole_0(sK1,X8) = k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X8))) ),
    inference(superposition,[],[f2560,f62])).

fof(f2560,plain,(
    ! [X1] : k5_xboole_0(sK1,X1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,X1))) ),
    inference(forward_demodulation,[],[f2502,f24])).

fof(f2502,plain,(
    ! [X1] : k5_xboole_0(sK1,X1) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK1),X1)) ),
    inference(superposition,[],[f24,f2494])).

fof(f181,plain,(
    ! [X33,X32] : k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X32,X33)))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X32,k4_xboole_0(sK1,X33))) ),
    inference(superposition,[],[f86,f130])).

fof(f2827,plain,(
    ! [X15] : k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X15,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X15,k4_xboole_0(sK1,sK0))) ),
    inference(superposition,[],[f54,f2679])).

fof(f742,plain,(
    ! [X1] : k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X1)) = k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X1,sK1)) ),
    inference(superposition,[],[f635,f634])).

fof(f634,plain,(
    ! [X5] : k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X5,k3_xboole_0(sK0,sK1))))) = k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X5)) ),
    inference(superposition,[],[f54,f86])).

fof(f635,plain,(
    ! [X6] : k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X6,k3_xboole_0(sK0,sK1))))) = k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X6,sK1)) ),
    inference(superposition,[],[f54,f181])).

fof(f749,plain,(
    ! [X2,X3] : k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,k4_xboole_0(X2,X3))) = k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X2,k4_xboole_0(sK1,X3))) ),
    inference(superposition,[],[f742,f165])).

fof(f165,plain,(
    ! [X6,X8,X7] : k3_xboole_0(k4_xboole_0(X7,X8),X6) = k3_xboole_0(X7,k4_xboole_0(X6,X8)) ),
    inference(superposition,[],[f130,f18])).

fof(f3506,plain,(
    ! [X14] : k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,sK0))) = k5_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,X14)),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f2681,f3496])).

fof(f2681,plain,(
    ! [X14] : k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,sK0))) = k5_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X14)),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f1430,f2679])).

fof(f1430,plain,(
    ! [X14] : k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) = k5_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X14)),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f1406,f23])).

fof(f1406,plain,(
    ! [X14] : k3_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(X14,sK1),k3_xboole_0(sK0,sK1))) = k5_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X14)),k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(X14,sK1),k3_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f40,f742])).

fof(f3833,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK0),sK0))) ),
    inference(forward_demodulation,[],[f3832,f2679])).

fof(f3832,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)),sK0))) ),
    inference(forward_demodulation,[],[f3831,f661])).

fof(f661,plain,(
    ! [X6,X4,X5] : k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X5,X6),X4)) = k2_xboole_0(X4,k3_xboole_0(X5,k4_xboole_0(X4,X6))) ),
    inference(superposition,[],[f633,f130])).

fof(f3831,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f3830,f3514])).

fof(f3830,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f3821,f23])).

fof(f3821,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f40,f2654])).

fof(f4313,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f4310,f2524])).

fof(f2524,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1844,f2523])).

fof(f2523,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2510,f20])).

fof(f2510,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f2357,f2505])).

fof(f2357,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f2147,f2354])).

fof(f2147,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) ),
    inference(forward_demodulation,[],[f2146,f1693])).

fof(f2146,plain,(
    k3_xboole_0(sK0,k3_xboole_0(sK0,k4_xboole_0(sK1,sK1))) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) ),
    inference(forward_demodulation,[],[f2145,f23])).

fof(f2145,plain,(
    k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) = k3_xboole_0(sK0,k4_xboole_0(k3_xboole_0(sK0,sK1),sK1)) ),
    inference(forward_demodulation,[],[f2144,f130])).

fof(f2144,plain,(
    k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) = k3_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2143,f18])).

fof(f2143,plain,(
    k3_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) ),
    inference(forward_demodulation,[],[f2137,f87])).

fof(f2137,plain,(
    k3_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f62,f1945])).

fof(f1945,plain,(
    k3_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(resolution,[],[f1942,f22])).

fof(f1942,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f1853,f1693])).

fof(f1853,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK0,k4_xboole_0(X0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f1776,f130])).

fof(f1776,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1749,f18])).

fof(f1749,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f196,f1693])).

fof(f196,plain,(
    ! [X2,X0,X3,X1] : r1_tarski(k3_xboole_0(X3,k3_xboole_0(X1,k4_xboole_0(X0,X2))),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f171,f52])).

fof(f171,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X1,k4_xboole_0(X0,X2)),X0) ),
    inference(superposition,[],[f17,f130])).

fof(f1844,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1843,f179])).

fof(f179,plain,(
    ! [X26,X27,X25] : k4_xboole_0(k4_xboole_0(X26,X27),X25) = k5_xboole_0(k4_xboole_0(X26,X27),k3_xboole_0(X26,k4_xboole_0(X25,X27))) ),
    inference(superposition,[],[f36,f130])).

fof(f1843,plain,(
    k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f1842,f23])).

fof(f1842,plain,(
    k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1808,f837])).

fof(f837,plain,(
    ! [X8] : k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(X8,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,X8)))) ),
    inference(superposition,[],[f56,f85])).

fof(f1808,plain,(
    k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,sK0)))) ),
    inference(superposition,[],[f837,f1775])).

fof(f4310,plain,(
    k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))) ),
    inference(backward_demodulation,[],[f2010,f4291])).

fof(f4291,plain,(
    ! [X0] : k4_xboole_0(k4_xboole_0(sK0,sK1),X0) = k3_xboole_0(sK0,k4_xboole_0(k5_xboole_0(sK1,sK1),X0)) ),
    inference(superposition,[],[f23,f3962])).

fof(f2010,plain,(
    k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))) = k3_xboole_0(sK0,k4_xboole_0(k5_xboole_0(sK1,sK1),sK1)) ),
    inference(forward_demodulation,[],[f2004,f165])).

fof(f2004,plain,(
    k3_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f21,f1795])).

fof(f3207,plain,(
    k4_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k2_xboole_0(sK1,k3_xboole_0(sK0,sK0)) ),
    inference(forward_demodulation,[],[f3206,f2973])).

fof(f2973,plain,(
    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k3_xboole_0(sK0,sK0)) ),
    inference(forward_demodulation,[],[f2948,f54])).

fof(f2948,plain,(
    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f19,f2524])).

fof(f3206,plain,(
    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f3154,f2524])).

fof(f3154,plain,(
    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)) ),
    inference(superposition,[],[f633,f3112])).

fof(f3112,plain,(
    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3111,f3104])).

fof(f3104,plain,(
    k4_xboole_0(sK0,sK1) = k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,k3_xboole_0(sK0,sK0))) ),
    inference(forward_demodulation,[],[f3103,f1693])).

fof(f3103,plain,(
    k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,k3_xboole_0(sK0,sK0))) ),
    inference(forward_demodulation,[],[f3087,f130])).

fof(f3087,plain,(
    k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,k3_xboole_0(sK0,sK0))) ),
    inference(superposition,[],[f40,f2973])).

fof(f3111,plain,(
    k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,k3_xboole_0(sK0,sK0))) ),
    inference(forward_demodulation,[],[f3091,f19])).

fof(f3091,plain,(
    k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK1,k3_xboole_0(sK0,sK0))) ),
    inference(superposition,[],[f21,f2973])).

fof(f2978,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK0)))) ),
    inference(backward_demodulation,[],[f1817,f2973])).

fof(f1817,plain,(
    k2_xboole_0(sK1,sK0) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f1093,f1806])).

fof(f1826,plain,(
    k5_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0))) = k3_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),sK1)) ),
    inference(backward_demodulation,[],[f1792,f1806])).

fof(f1792,plain,(
    k5_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),sK1)) ),
    inference(forward_demodulation,[],[f1791,f231])).

fof(f231,plain,(
    ! [X12,X10,X11,X9] : k3_xboole_0(X11,k4_xboole_0(k4_xboole_0(X9,X10),X12)) = k3_xboole_0(X9,k4_xboole_0(k4_xboole_0(X11,X12),X10)) ),
    inference(superposition,[],[f165,f130])).

fof(f1791,plain,(
    k5_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1788,f130])).

fof(f1788,plain,(
    k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) = k5_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f40,f1748])).

fof(f3845,plain,(
    k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1753,f3844])).

fof(f3844,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3843,f18])).

fof(f3843,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f3842,f3522])).

fof(f3522,plain,(
    ! [X4] : k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X4,sK1)) = k3_xboole_0(sK0,k3_xboole_0(sK1,X4)) ),
    inference(backward_demodulation,[],[f3495,f3521])).

fof(f3521,plain,(
    ! [X3] : k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,X3),k2_xboole_0(sK0,k3_xboole_0(sK1,X3))))) = k3_xboole_0(sK0,k3_xboole_0(sK1,X3)) ),
    inference(backward_demodulation,[],[f3504,f3519])).

fof(f3519,plain,(
    ! [X2] : k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X2)) = k3_xboole_0(sK0,k3_xboole_0(sK1,X2)) ),
    inference(forward_demodulation,[],[f3508,f21])).

fof(f3508,plain,(
    ! [X2] : k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK1,X2)),k2_xboole_0(sK0,k3_xboole_0(sK1,X2))) ),
    inference(backward_demodulation,[],[f3370,f3496])).

fof(f3370,plain,(
    ! [X2] : k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK1,X2)),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X2))) ),
    inference(backward_demodulation,[],[f110,f3367])).

fof(f110,plain,(
    ! [X2] : k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X2)) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,X2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X2))) ),
    inference(superposition,[],[f21,f86])).

fof(f3504,plain,(
    ! [X3] : k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X3)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,X3),k2_xboole_0(sK0,k3_xboole_0(sK1,X3))))) ),
    inference(backward_demodulation,[],[f487,f3496])).

fof(f487,plain,(
    ! [X3] : k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X3)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,X3),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X3))))) ),
    inference(superposition,[],[f114,f62])).

fof(f114,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK1,X0),X1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,X0),X1))) ),
    inference(forward_demodulation,[],[f113,f24])).

fof(f113,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK1,X0),X1)) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK1,X0)),X1)) ),
    inference(forward_demodulation,[],[f109,f24])).

fof(f109,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK1,X0),X1)) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,X0))),X1) ),
    inference(superposition,[],[f24,f86])).

fof(f3495,plain,(
    ! [X4] : k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X4,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,X4),k2_xboole_0(sK0,k3_xboole_0(sK1,X4))))) ),
    inference(backward_demodulation,[],[f524,f3494])).

fof(f524,plain,(
    ! [X4] : k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X4,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,X4),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X4,sK1))))) ),
    inference(superposition,[],[f124,f62])).

fof(f124,plain,(
    ! [X0,X1] : k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,X0),X1))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(X0,sK1),X1)) ),
    inference(forward_demodulation,[],[f123,f24])).

fof(f123,plain,(
    ! [X0,X1] : k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK1,X0)),X1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(X0,sK1),X1)) ),
    inference(forward_demodulation,[],[f119,f24])).

fof(f119,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,X0))),X1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(X0,sK1),X1)) ),
    inference(superposition,[],[f24,f87])).

fof(f3842,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f3841,f2536])).

fof(f2536,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2535,f1753])).

fof(f2535,plain,(
    k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2511,f20])).

fof(f2511,plain,(
    k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f2383,f2505])).

fof(f2383,plain,(
    k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f833,f2354])).

fof(f3841,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3840,f36])).

fof(f3840,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3823,f3369])).

fof(f3369,plain,(
    ! [X2] : k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X2,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,X2)) ),
    inference(backward_demodulation,[],[f87,f3367])).

fof(f3823,plain,(
    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f21,f2654])).

fof(f1753,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f20,f1693])).

fof(f3850,plain,(
    k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f2536,f3844])).

fof(f5311,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f19,f4657])).

fof(f4657,plain,(
    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4613,f4629])).

fof(f4613,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f4021,f4573])).

fof(f4021,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3996,f3850])).

fof(f3996,plain,(
    k4_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f881,f3994])).

fof(f3994,plain,(
    k3_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f3993,f3940])).

fof(f3993,plain,(
    k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f3933,f3959])).

fof(f3933,plain,(
    k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)) ),
    inference(superposition,[],[f633,f3900])).

fof(f881,plain,(
    k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,k5_xboole_0(sK1,sK1))) = k4_xboole_0(sK0,k5_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f847,f20])).

fof(f847,plain,(
    k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,k5_xboole_0(sK1,sK1))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f56,f76])).

fof(f76,plain,(
    k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,k5_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f21,f63])).

fof(f4671,plain,(
    ! [X1] : k5_xboole_0(sK1,k5_xboole_0(sK1,X1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,sK1),X1)) ),
    inference(backward_demodulation,[],[f3859,f4668])).

fof(f4668,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_xboole_0(sK0,sK1),X0) ),
    inference(forward_demodulation,[],[f4667,f1693])).

fof(f4667,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)),X0) ),
    inference(forward_demodulation,[],[f4618,f130])).

fof(f4618,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)),X0) ),
    inference(backward_demodulation,[],[f4269,f4573])).

fof(f4269,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)),X0) ),
    inference(forward_demodulation,[],[f4268,f18])).

fof(f4268,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK1),sK1),X0) ),
    inference(forward_demodulation,[],[f4267,f2494])).

fof(f4267,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK1),sK1),X0) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,X0)) ),
    inference(forward_demodulation,[],[f4263,f24])).

fof(f4263,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK1),sK1),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK1),sK1),k5_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f58,f3916])).

fof(f3916,plain,(
    sK1 = k2_xboole_0(k5_xboole_0(sK1,sK1),sK1) ),
    inference(superposition,[],[f177,f3900])).

fof(f3859,plain,(
    ! [X1] : k5_xboole_0(k4_xboole_0(sK0,sK1),X1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,sK1),X1)) ),
    inference(superposition,[],[f24,f2756])).

fof(f5332,plain,(
    ! [X0] : k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,X0))) = k5_xboole_0(sK0,X0) ),
    inference(backward_demodulation,[],[f77,f5331])).

fof(f6739,plain,(
    ! [X16] : k4_xboole_0(sK0,k4_xboole_0(sK0,X16)) = k5_xboole_0(sK0,k4_xboole_0(sK0,X16)) ),
    inference(superposition,[],[f20,f5883])).

fof(f5883,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k3_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(superposition,[],[f23,f5486])).

fof(f5486,plain,(
    sK0 = k3_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f4629,f5331])).

fof(f6756,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(backward_demodulation,[],[f5997,f6739])).

fof(f5997,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k5_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    inference(forward_demodulation,[],[f5996,f5813])).

fof(f5813,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k2_xboole_0(k4_xboole_0(sK0,sK0),k3_xboole_0(X0,sK0)) ),
    inference(forward_demodulation,[],[f5812,f5602])).

fof(f5602,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f4585,f5590])).

fof(f5590,plain,(
    ! [X3] : k3_xboole_0(sK0,k4_xboole_0(sK1,X3)) = k4_xboole_0(sK0,X3) ),
    inference(forward_demodulation,[],[f5454,f20])).

fof(f5454,plain,(
    ! [X3] : k3_xboole_0(sK0,k4_xboole_0(sK1,X3)) = k5_xboole_0(sK0,k3_xboole_0(sK0,X3)) ),
    inference(backward_demodulation,[],[f4058,f5331])).

fof(f4058,plain,(
    ! [X3] : k3_xboole_0(sK0,k4_xboole_0(sK1,X3)) = k5_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK1),X3)) ),
    inference(forward_demodulation,[],[f4057,f23])).

fof(f4057,plain,(
    ! [X3] : k4_xboole_0(k3_xboole_0(sK0,sK1),X3) = k5_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK1),X3)) ),
    inference(forward_demodulation,[],[f4056,f20])).

fof(f4056,plain,(
    ! [X3] : k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),X3)) = k5_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK1),X3)) ),
    inference(forward_demodulation,[],[f4010,f853])).

fof(f853,plain,(
    ! [X35,X36,X34] : k5_xboole_0(k4_xboole_0(X34,X35),k5_xboole_0(X36,k2_xboole_0(k3_xboole_0(X34,X35),X36))) = k5_xboole_0(X34,k3_xboole_0(k3_xboole_0(X34,X35),X36)) ),
    inference(superposition,[],[f56,f62])).

fof(f4010,plain,(
    ! [X3] : k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),X3)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(X3,k2_xboole_0(k3_xboole_0(sK0,sK1),X3))) ),
    inference(backward_demodulation,[],[f3969,f3994])).

fof(f3969,plain,(
    ! [X3] : k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)),X3)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(X3,k2_xboole_0(k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)),X3))) ),
    inference(backward_demodulation,[],[f428,f3962])).

fof(f428,plain,(
    ! [X3] : k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k5_xboole_0(X3,k2_xboole_0(k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)),X3))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)),X3)) ),
    inference(superposition,[],[f98,f62])).

fof(f98,plain,(
    ! [X0] : k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)),X0)) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)),X0) ),
    inference(superposition,[],[f24,f76])).

fof(f4585,plain,(
    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(backward_demodulation,[],[f3900,f4573])).

fof(f5812,plain,(
    ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(X0,sK0)) ),
    inference(forward_demodulation,[],[f5313,f886])).

fof(f886,plain,(
    ! [X28,X29,X27] : k5_xboole_0(k4_xboole_0(X27,X28),k3_xboole_0(X29,k3_xboole_0(X27,X28))) = k4_xboole_0(X27,k4_xboole_0(X28,X29)) ),
    inference(forward_demodulation,[],[f885,f20])).

fof(f885,plain,(
    ! [X28,X29,X27] : k5_xboole_0(k4_xboole_0(X27,X28),k3_xboole_0(X29,k3_xboole_0(X27,X28))) = k5_xboole_0(X27,k3_xboole_0(X27,k4_xboole_0(X28,X29))) ),
    inference(forward_demodulation,[],[f851,f23])).

fof(f851,plain,(
    ! [X28,X29,X27] : k5_xboole_0(k4_xboole_0(X27,X28),k3_xboole_0(X29,k3_xboole_0(X27,X28))) = k5_xboole_0(X27,k4_xboole_0(k3_xboole_0(X27,X28),X29)) ),
    inference(superposition,[],[f56,f36])).

fof(f5313,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(X0,sK0)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(X0,k3_xboole_0(sK0,sK1))) ),
    inference(superposition,[],[f54,f4657])).

fof(f5996,plain,(
    ! [X0] : k5_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k2_xboole_0(k4_xboole_0(sK0,sK0),k3_xboole_0(X0,sK0)) ),
    inference(forward_demodulation,[],[f5995,f36])).

fof(f5995,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(sK0,sK0),k3_xboole_0(X0,sK0)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(X0,sK0))) ),
    inference(forward_demodulation,[],[f5975,f5774])).

fof(f5774,plain,(
    ! [X0] : k5_xboole_0(sK0,k5_xboole_0(sK0,X0)) = k5_xboole_0(k4_xboole_0(sK0,sK0),X0) ),
    inference(backward_demodulation,[],[f5690,f5498])).

fof(f5690,plain,(
    ! [X0] : k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_xboole_0(sK0,sK0),X0) ),
    inference(backward_demodulation,[],[f4668,f5602])).

fof(f5975,plain,(
    ! [X0] : k2_xboole_0(k4_xboole_0(sK0,sK0),k3_xboole_0(X0,sK0)) = k5_xboole_0(k4_xboole_0(sK0,sK0),k3_xboole_0(X0,sK0)) ),
    inference(superposition,[],[f54,f5761])).

fof(f5761,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) ),
    inference(forward_demodulation,[],[f5496,f5602])).

fof(f5496,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f4657,f5331])).

fof(f6576,plain,(
    ! [X6] : r1_tarski(k4_xboole_0(sK0,X6),sK1) ),
    inference(superposition,[],[f171,f5590])).

fof(f16,plain,(
    ~ r1_tarski(k3_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 11:07:07 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.48  % (6711)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (6702)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (6704)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (6710)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (6700)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (6714)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.50  % (6703)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (6706)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (6708)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (6707)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (6713)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.52  % (6715)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (6699)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.53  % (6705)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (6701)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.54  % (6712)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.56  % (6716)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.57  % (6709)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 4.69/0.99  % (6715)Refutation found. Thanks to Tanya!
% 4.69/0.99  % SZS status Theorem for theBenchmark
% 4.69/0.99  % SZS output start Proof for theBenchmark
% 4.69/0.99  fof(f7937,plain,(
% 4.69/0.99    $false),
% 4.69/0.99    inference(subsumption_resolution,[],[f16,f7892])).
% 4.69/0.99  fof(f7892,plain,(
% 4.69/0.99    ( ! [X2] : (r1_tarski(k3_xboole_0(sK0,X2),sK1)) )),
% 4.69/0.99    inference(superposition,[],[f6576,f7828])).
% 4.69/0.99  fof(f7828,plain,(
% 4.69/0.99    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k3_xboole_0(sK0,X0)) )),
% 4.69/0.99    inference(backward_demodulation,[],[f6756,f7760])).
% 4.69/0.99  fof(f7760,plain,(
% 4.69/0.99    ( ! [X16] : (k3_xboole_0(sK0,X16) = k4_xboole_0(sK0,k4_xboole_0(sK0,X16))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f6739,f7758])).
% 4.69/0.99  fof(f7758,plain,(
% 4.69/0.99    ( ! [X10] : (k3_xboole_0(sK0,X10) = k5_xboole_0(sK0,k4_xboole_0(sK0,X10))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f7739,f20])).
% 4.69/0.99  fof(f20,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.69/0.99    inference(cnf_transformation,[],[f2])).
% 4.69/0.99  fof(f2,axiom,(
% 4.69/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.69/0.99  fof(f7739,plain,(
% 4.69/0.99    ( ! [X10] : (k3_xboole_0(sK0,X10) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,X10)))) )),
% 4.69/0.99    inference(superposition,[],[f5771,f62])).
% 4.69/0.99  fof(f62,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 4.69/0.99    inference(superposition,[],[f24,f21])).
% 4.69/0.99  fof(f21,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 4.69/0.99    inference(cnf_transformation,[],[f7])).
% 4.69/0.99  fof(f7,axiom,(
% 4.69/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 4.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 4.69/0.99  fof(f24,plain,(
% 4.69/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.69/0.99    inference(cnf_transformation,[],[f6])).
% 4.69/0.99  fof(f6,axiom,(
% 4.69/0.99    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.69/0.99  fof(f5771,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(sK0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK0,X0)))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f5332,f5498])).
% 4.69/0.99  fof(f5498,plain,(
% 4.69/0.99    ( ! [X1] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,X1))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f4671,f5331])).
% 4.69/0.99  fof(f5331,plain,(
% 4.69/0.99    sK0 = k3_xboole_0(sK0,sK1)),
% 4.69/0.99    inference(forward_demodulation,[],[f5330,f1756])).
% 4.69/0.99  fof(f1756,plain,(
% 4.69/0.99    sK0 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 4.69/0.99    inference(superposition,[],[f30,f1693])).
% 4.69/0.99  fof(f1693,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k4_xboole_0(sK0,sK1)),
% 4.69/0.99    inference(forward_demodulation,[],[f1688,f20])).
% 4.69/0.99  fof(f1688,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(backward_demodulation,[],[f111,f1683])).
% 4.69/0.99  fof(f1683,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f1682,f63])).
% 4.69/0.99  fof(f63,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(superposition,[],[f24,f44])).
% 4.69/0.99  fof(f44,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),sK1)),
% 4.69/0.99    inference(superposition,[],[f21,f29])).
% 4.69/0.99  fof(f29,plain,(
% 4.69/0.99    sK1 = k2_xboole_0(sK0,sK1)),
% 4.69/0.99    inference(resolution,[],[f22,f15])).
% 4.69/0.99  fof(f15,plain,(
% 4.69/0.99    r1_tarski(sK0,sK1)),
% 4.69/0.99    inference(cnf_transformation,[],[f14])).
% 4.69/0.99  fof(f14,plain,(
% 4.69/0.99    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 4.69/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f13])).
% 4.69/0.99  fof(f13,plain,(
% 4.69/0.99    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (~r1_tarski(k3_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 4.69/0.99    introduced(choice_axiom,[])).
% 4.69/0.99  fof(f11,plain,(
% 4.69/0.99    ? [X0,X1,X2] : (~r1_tarski(k3_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 4.69/0.99    inference(ennf_transformation,[],[f10])).
% 4.69/0.99  fof(f10,negated_conjecture,(
% 4.69/0.99    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 4.69/0.99    inference(negated_conjecture,[],[f9])).
% 4.69/0.99  fof(f9,conjecture,(
% 4.69/0.99    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 4.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 4.69/0.99  fof(f22,plain,(
% 4.69/0.99    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 4.69/0.99    inference(cnf_transformation,[],[f12])).
% 4.69/0.99  fof(f12,plain,(
% 4.69/0.99    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 4.69/0.99    inference(ennf_transformation,[],[f3])).
% 4.69/0.99  fof(f3,axiom,(
% 4.69/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 4.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 4.69/0.99  fof(f1682,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f1679,f29])).
% 4.69/0.99  fof(f1679,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(superposition,[],[f55,f1668])).
% 4.69/0.99  fof(f1668,plain,(
% 4.69/0.99    k5_xboole_0(sK1,sK1) = k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f1667,f29])).
% 4.69/0.99  fof(f1667,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k5_xboole_0(k2_xboole_0(sK0,sK1),sK1)),
% 4.69/0.99    inference(forward_demodulation,[],[f1661,f55])).
% 4.69/0.99  fof(f1661,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),sK1))),
% 4.69/0.99    inference(superposition,[],[f1149,f1654])).
% 4.69/0.99  fof(f1654,plain,(
% 4.69/0.99    sK1 = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(superposition,[],[f1651,f77])).
% 4.69/0.99  fof(f77,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(k3_xboole_0(sK0,sK1),X0) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,X0)))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f75,f24])).
% 4.69/0.99  fof(f75,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(k3_xboole_0(sK0,sK1),X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,sK1),X0))) )),
% 4.69/0.99    inference(superposition,[],[f24,f63])).
% 4.69/0.99  fof(f1651,plain,(
% 4.69/0.99    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 4.69/0.99    inference(backward_demodulation,[],[f1650,f1646])).
% 4.69/0.99  fof(f1646,plain,(
% 4.69/0.99    k5_xboole_0(sK1,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))))),
% 4.69/0.99    inference(superposition,[],[f55,f1352])).
% 4.69/0.99  fof(f1352,plain,(
% 4.69/0.99    k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))))),
% 4.69/0.99    inference(backward_demodulation,[],[f1166,f1339])).
% 4.69/0.99  fof(f1339,plain,(
% 4.69/0.99    k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(superposition,[],[f1126,f1310])).
% 4.69/0.99  fof(f1310,plain,(
% 4.69/0.99    ( ! [X26,X25] : (k5_xboole_0(k4_xboole_0(sK1,X25),k3_xboole_0(k3_xboole_0(X25,sK1),X26)) = k4_xboole_0(sK1,k4_xboole_0(X25,X26))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f1309,f1128])).
% 4.69/0.99  fof(f1128,plain,(
% 4.69/0.99    ( ! [X2,X3] : (k4_xboole_0(sK1,k4_xboole_0(X2,X3)) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(X2,k4_xboole_0(sK1,X3))))) )),
% 4.69/0.99    inference(superposition,[],[f1118,f130])).
% 4.69/0.99  fof(f130,plain,(
% 4.69/0.99    ( ! [X4,X5,X3] : (k3_xboole_0(X3,k4_xboole_0(X4,X5)) = k3_xboole_0(X4,k4_xboole_0(X3,X5))) )),
% 4.69/0.99    inference(superposition,[],[f52,f23])).
% 4.69/0.99  fof(f23,plain,(
% 4.69/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 4.69/0.99    inference(cnf_transformation,[],[f5])).
% 4.69/0.99  fof(f5,axiom,(
% 4.69/0.99    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 4.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 4.69/0.99  fof(f52,plain,(
% 4.69/0.99    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X1,X0),X2)) )),
% 4.69/0.99    inference(superposition,[],[f23,f18])).
% 4.69/0.99  fof(f18,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.69/0.99    inference(cnf_transformation,[],[f1])).
% 4.69/0.99  fof(f1,axiom,(
% 4.69/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.69/0.99  fof(f1118,plain,(
% 4.69/0.99    ( ! [X1] : (k4_xboole_0(sK1,X1) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,X1)))) )),
% 4.69/0.99    inference(superposition,[],[f1083,f162])).
% 4.69/0.99  fof(f162,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,X0),X1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(X0,k5_xboole_0(k2_xboole_0(sK1,X0),X1)))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f161,f24])).
% 4.69/0.99  fof(f161,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(sK1,X0)),X1)) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,X0),X1))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f159,f24])).
% 4.69/0.99  fof(f159,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(X0,k2_xboole_0(sK1,X0)),X1)) = k5_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,X0)),X1)) )),
% 4.69/0.99    inference(superposition,[],[f24,f152])).
% 4.69/0.99  fof(f152,plain,(
% 4.69/0.99    ( ! [X8] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(X8,k2_xboole_0(sK1,X8))) = k5_xboole_0(sK0,k4_xboole_0(sK1,X8))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f145,f20])).
% 4.69/0.99  fof(f145,plain,(
% 4.69/0.99    ( ! [X8] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(X8,k2_xboole_0(sK1,X8))) = k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,X8)))) )),
% 4.69/0.99    inference(superposition,[],[f77,f62])).
% 4.69/0.99  fof(f1083,plain,(
% 4.69/0.99    ( ! [X0] : (k4_xboole_0(sK1,X0) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,X0))))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f1082,f36])).
% 4.69/0.99  fof(f36,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 4.69/0.99    inference(superposition,[],[f20,f18])).
% 4.69/0.99  fof(f1082,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,X0)))) = k5_xboole_0(sK1,k3_xboole_0(X0,sK1))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f1081,f29])).
% 4.69/0.99  fof(f1081,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,X0)))) = k5_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(X0,sK1))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f1074,f55])).
% 4.69/0.99  fof(f1074,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(X0,sK1))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,X0))))) )),
% 4.69/0.99    inference(superposition,[],[f162,f1055])).
% 4.69/0.99  fof(f1055,plain,(
% 4.69/0.99    ( ! [X1] : (k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(X1,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,X1))) )),
% 4.69/0.99    inference(superposition,[],[f973,f55])).
% 4.69/0.99  fof(f973,plain,(
% 4.69/0.99    ( ! [X1] : (k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(X1,sK1)) = k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK1,X1)))) )),
% 4.69/0.99    inference(superposition,[],[f55,f958])).
% 4.69/0.99  fof(f958,plain,(
% 4.69/0.99    ( ! [X1] : (k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(X1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK1,X1))) )),
% 4.69/0.99    inference(superposition,[],[f833,f832])).
% 4.69/0.99  fof(f832,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK1,X0)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,X0))))) )),
% 4.69/0.99    inference(superposition,[],[f56,f86])).
% 4.69/0.99  fof(f86,plain,(
% 4.69/0.99    ( ! [X1] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,X1)))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f79,f24])).
% 4.69/0.99  fof(f79,plain,(
% 4.69/0.99    ( ! [X1] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK1,X1))) )),
% 4.69/0.99    inference(superposition,[],[f59,f20])).
% 4.69/0.99  fof(f59,plain,(
% 4.69/0.99    ( ! [X12] : (k5_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK1,X12)) = k5_xboole_0(k3_xboole_0(sK0,sK1),X12)) )),
% 4.69/0.99    inference(superposition,[],[f24,f44])).
% 4.69/0.99  fof(f56,plain,(
% 4.69/0.99    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(k3_xboole_0(X3,X4),X5)) = k5_xboole_0(k4_xboole_0(X3,X4),X5)) )),
% 4.69/0.99    inference(superposition,[],[f24,f20])).
% 4.69/0.99  fof(f833,plain,(
% 4.69/0.99    ( ! [X1] : (k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(X1,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,X1))))) )),
% 4.69/0.99    inference(superposition,[],[f56,f87])).
% 4.69/0.99  fof(f87,plain,(
% 4.69/0.99    ( ! [X2] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X2,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,X2)))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f80,f24])).
% 4.69/0.99  fof(f80,plain,(
% 4.69/0.99    ( ! [X2] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X2,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k4_xboole_0(sK1,X2))) )),
% 4.69/0.99    inference(superposition,[],[f59,f36])).
% 4.69/0.99  fof(f1309,plain,(
% 4.69/0.99    ( ! [X26,X25] : (k5_xboole_0(k4_xboole_0(sK1,X25),k3_xboole_0(k3_xboole_0(X25,sK1),X26)) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(X25,k4_xboole_0(sK1,X26))))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f1280,f23])).
% 4.69/0.99  fof(f1280,plain,(
% 4.69/0.99    ( ! [X26,X25] : (k5_xboole_0(k4_xboole_0(sK1,X25),k3_xboole_0(k3_xboole_0(X25,sK1),X26)) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k3_xboole_0(X25,sK1),X26)))) )),
% 4.69/0.99    inference(superposition,[],[f1149,f20])).
% 4.69/0.99  fof(f1126,plain,(
% 4.69/0.99    ( ! [X0] : (k4_xboole_0(sK1,X0) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(X0,sK1)))) )),
% 4.69/0.99    inference(superposition,[],[f1118,f18])).
% 4.69/0.99  fof(f1166,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k5_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(superposition,[],[f56,f1093])).
% 4.69/0.99  fof(f1093,plain,(
% 4.69/0.99    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))))),
% 4.69/0.99    inference(forward_demodulation,[],[f1092,f659])).
% 4.69/0.99  fof(f659,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X0)) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.69/0.99    inference(superposition,[],[f633,f18])).
% 4.69/0.99  fof(f633,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.69/0.99    inference(superposition,[],[f54,f20])).
% 4.69/0.99  fof(f54,plain,(
% 4.69/0.99    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k3_xboole_0(X0,X1)) = k5_xboole_0(X2,k3_xboole_0(X0,k4_xboole_0(X1,X2)))) )),
% 4.69/0.99    inference(superposition,[],[f19,f23])).
% 4.69/0.99  fof(f19,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.69/0.99    inference(cnf_transformation,[],[f8])).
% 4.69/0.99  fof(f8,axiom,(
% 4.69/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 4.69/0.99  fof(f1092,plain,(
% 4.69/0.99    k2_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))))),
% 4.69/0.99    inference(forward_demodulation,[],[f1091,f54])).
% 4.69/0.99  fof(f1091,plain,(
% 4.69/0.99    k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k5_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f1090,f29])).
% 4.69/0.99  fof(f1090,plain,(
% 4.69/0.99    k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k5_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f1087,f55])).
% 4.69/0.99  fof(f1087,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))))),
% 4.69/0.99    inference(superposition,[],[f162,f1067])).
% 4.69/0.99  fof(f1067,plain,(
% 4.69/0.99    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f1066,f130])).
% 4.69/0.99  fof(f1066,plain,(
% 4.69/0.99    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f1065,f18])).
% 4.69/0.99  fof(f1065,plain,(
% 4.69/0.99    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f1053,f19])).
% 4.69/0.99  fof(f1053,plain,(
% 4.69/0.99    k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(k4_xboole_0(sK0,sK1),sK1)) = k5_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),
% 4.69/0.99    inference(superposition,[],[f973,f36])).
% 4.69/0.99  fof(f1650,plain,(
% 4.69/0.99    sK1 = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))))))),
% 4.69/0.99    inference(forward_demodulation,[],[f1649,f31])).
% 4.69/0.99  fof(f31,plain,(
% 4.69/0.99    ( ! [X2,X3] : (k2_xboole_0(k3_xboole_0(X2,X3),X3) = X3) )),
% 4.69/0.99    inference(resolution,[],[f22,f25])).
% 4.69/0.99  fof(f25,plain,(
% 4.69/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 4.69/0.99    inference(superposition,[],[f17,f18])).
% 4.69/0.99  fof(f17,plain,(
% 4.69/0.99    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.69/0.99    inference(cnf_transformation,[],[f4])).
% 4.69/0.99  fof(f4,axiom,(
% 4.69/0.99    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.69/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 4.69/0.99  fof(f1649,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))))) = k2_xboole_0(k3_xboole_0(sK0,sK1),sK1)),
% 4.69/0.99    inference(forward_demodulation,[],[f1645,f19])).
% 4.69/0.99  fof(f1645,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(superposition,[],[f104,f1352])).
% 4.69/0.99  fof(f104,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(X0,sK1),X1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(sK1,X0),X1)))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f103,f24])).
% 4.69/0.99  fof(f103,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(X0,sK1),X1)) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k2_xboole_0(sK1,X0)),X1))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f101,f24])).
% 4.69/0.99  fof(f101,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k4_xboole_0(X0,sK1),X1)) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,X0))),X1)) )),
% 4.69/0.99    inference(superposition,[],[f24,f85])).
% 4.69/0.99  fof(f85,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(X0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,X0)))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f78,f24])).
% 4.69/0.99  fof(f78,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(X0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK1,X0))) )),
% 4.69/0.99    inference(superposition,[],[f59,f19])).
% 4.69/0.99  fof(f1149,plain,(
% 4.69/0.99    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(sK1,X1),X2) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(k3_xboole_0(X1,sK1),X2)))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f1145,f24])).
% 4.69/0.99  fof(f1145,plain,(
% 4.69/0.99    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(sK1,X1),X2) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(X1,sK1)),X2))) )),
% 4.69/0.99    inference(superposition,[],[f24,f1126])).
% 4.69/0.99  fof(f55,plain,(
% 4.69/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X2)) = k5_xboole_0(k2_xboole_0(X0,X1),X2)) )),
% 4.69/0.99    inference(superposition,[],[f24,f19])).
% 4.69/0.99  fof(f111,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f107,f23])).
% 4.69/0.99  fof(f107,plain,(
% 4.69/0.99    k4_xboole_0(k3_xboole_0(sK0,sK1),sK1) = k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),
% 4.69/0.99    inference(superposition,[],[f86,f36])).
% 4.69/0.99  fof(f30,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = X0) )),
% 4.69/0.99    inference(resolution,[],[f22,f17])).
% 4.69/0.99  fof(f5330,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)),
% 4.69/0.99    inference(forward_demodulation,[],[f5311,f4634])).
% 4.69/0.99  fof(f4634,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(backward_demodulation,[],[f3850,f4629])).
% 4.69/0.99  fof(f4629,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(backward_demodulation,[],[f3845,f4574])).
% 4.69/0.99  fof(f4574,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(backward_demodulation,[],[f63,f4573])).
% 4.69/0.99  fof(f4573,plain,(
% 4.69/0.99    k5_xboole_0(sK1,sK1) = k4_xboole_0(sK0,sK1)),
% 4.69/0.99    inference(forward_demodulation,[],[f4572,f1693])).
% 4.69/0.99  fof(f4572,plain,(
% 4.69/0.99    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f4401,f1748])).
% 4.69/0.99  fof(f1748,plain,(
% 4.69/0.99    sK1 = k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 4.69/0.99    inference(superposition,[],[f177,f1693])).
% 4.69/0.99  fof(f177,plain,(
% 4.69/0.99    ( ! [X21,X19,X20] : (k2_xboole_0(k3_xboole_0(X20,k4_xboole_0(X19,X21)),X19) = X19) )),
% 4.69/0.99    inference(superposition,[],[f30,f130])).
% 4.69/0.99  fof(f4401,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),sK1))),
% 4.69/0.99    inference(backward_demodulation,[],[f1826,f4385])).
% 4.69/0.99  fof(f4385,plain,(
% 4.69/0.99    sK1 = k2_xboole_0(sK1,sK0)),
% 4.69/0.99    inference(forward_demodulation,[],[f4384,f2579])).
% 4.69/0.99  fof(f2579,plain,(
% 4.69/0.99    sK1 = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(backward_demodulation,[],[f2355,f2576])).
% 4.69/0.99  fof(f2576,plain,(
% 4.69/0.99    sK1 = k5_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f2575,f29])).
% 4.69/0.99  fof(f2575,plain,(
% 4.69/0.99    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f2574,f19])).
% 4.69/0.99  fof(f2574,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f2573,f36])).
% 4.69/0.99  fof(f2573,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k5_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f2563,f2355])).
% 4.69/0.99  fof(f2563,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(superposition,[],[f77,f2509])).
% 4.69/0.99  fof(f2509,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(backward_demodulation,[],[f2354,f2505])).
% 4.69/0.99  fof(f2505,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2504,f63])).
% 4.69/0.99  fof(f2504,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2499,f148])).
% 4.69/0.99  fof(f148,plain,(
% 4.69/0.99    ( ! [X2,X3] : (k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X3)) = k3_xboole_0(X3,k3_xboole_0(X2,X3))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f136,f18])).
% 4.69/0.99  fof(f136,plain,(
% 4.69/0.99    ( ! [X2,X3] : (k3_xboole_0(k3_xboole_0(X2,X3),X3) = k5_xboole_0(k3_xboole_0(X2,X3),k5_xboole_0(X3,X3))) )),
% 4.69/0.99    inference(superposition,[],[f62,f31])).
% 4.69/0.99  fof(f2499,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(superposition,[],[f77,f2494])).
% 4.69/0.99  fof(f2494,plain,(
% 4.69/0.99    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2489,f29])).
% 4.69/0.99  fof(f2489,plain,(
% 4.69/0.99    sK1 = k5_xboole_0(k2_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(superposition,[],[f2133,f55])).
% 4.69/0.99  fof(f2133,plain,(
% 4.69/0.99    sK1 = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f2132,f29])).
% 4.69/0.99  fof(f2132,plain,(
% 4.69/0.99    k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f2131,f19])).
% 4.69/0.99  fof(f2131,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f2128,f152])).
% 4.69/0.99  fof(f2128,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,sK0)))),
% 4.69/0.99    inference(superposition,[],[f162,f2007])).
% 4.69/0.99  fof(f2007,plain,(
% 4.69/0.99    k2_xboole_0(sK1,sK0) = k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2002,f19])).
% 4.69/0.99  fof(f2002,plain,(
% 4.69/0.99    k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(superposition,[],[f55,f1795])).
% 4.69/0.99  fof(f1795,plain,(
% 4.69/0.99    k4_xboole_0(sK0,sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f1794,f1693])).
% 4.69/0.99  fof(f1794,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f1793,f130])).
% 4.69/0.99  fof(f1793,plain,(
% 4.69/0.99    k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f1789,f18])).
% 4.69/0.99  fof(f1789,plain,(
% 4.69/0.99    k3_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(superposition,[],[f62,f1748])).
% 4.69/0.99  fof(f2354,plain,(
% 4.69/0.99    k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(backward_demodulation,[],[f1813,f2353])).
% 4.69/0.99  fof(f2353,plain,(
% 4.69/0.99    k4_xboole_0(sK1,sK0) = k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f2352,f36])).
% 4.69/0.99  fof(f2352,plain,(
% 4.69/0.99    k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f2351,f18])).
% 4.69/0.99  fof(f2351,plain,(
% 4.69/0.99    k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f2350,f63])).
% 4.69/0.99  fof(f2350,plain,(
% 4.69/0.99    k5_xboole_0(k3_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k5_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f2265,f24])).
% 4.69/0.99  fof(f2265,plain,(
% 4.69/0.99    k5_xboole_0(k3_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k5_xboole_0(k5_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(superposition,[],[f58,f1965])).
% 4.69/0.99  fof(f1965,plain,(
% 4.69/0.99    k5_xboole_0(sK1,sK1) = k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(superposition,[],[f55,f1925])).
% 4.69/0.99  fof(f1925,plain,(
% 4.69/0.99    sK1 = k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f1878,f1748])).
% 4.69/0.99  fof(f1878,plain,(
% 4.69/0.99    k2_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(superposition,[],[f19,f1806])).
% 4.69/0.99  fof(f1806,plain,(
% 4.69/0.99    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK0)),
% 4.69/0.99    inference(superposition,[],[f1775,f659])).
% 4.69/0.99  fof(f1775,plain,(
% 4.69/0.99    k2_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,sK0)),
% 4.69/0.99    inference(forward_demodulation,[],[f1745,f19])).
% 4.69/0.99  fof(f1745,plain,(
% 4.69/0.99    k2_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(superposition,[],[f54,f1693])).
% 4.69/0.99  fof(f58,plain,(
% 4.69/0.99    ( ! [X10,X11,X9] : (k5_xboole_0(k5_xboole_0(X9,X10),k5_xboole_0(k2_xboole_0(X9,X10),X11)) = k5_xboole_0(k3_xboole_0(X9,X10),X11)) )),
% 4.69/0.99    inference(superposition,[],[f24,f21])).
% 4.69/0.99  fof(f1813,plain,(
% 4.69/0.99    k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0)))),
% 4.69/0.99    inference(superposition,[],[f62,f1775])).
% 4.69/0.99  fof(f2355,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(backward_demodulation,[],[f1810,f2353])).
% 4.69/0.99  fof(f1810,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0)))),
% 4.69/0.99    inference(superposition,[],[f152,f1775])).
% 4.69/0.99  fof(f4384,plain,(
% 4.69/0.99    k2_xboole_0(sK1,sK0) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f4363,f2698])).
% 4.69/0.99  fof(f2698,plain,(
% 4.69/0.99    k4_xboole_0(sK1,sK0) = k5_xboole_0(sK0,k2_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(backward_demodulation,[],[f1821,f2679])).
% 4.69/0.99  fof(f2679,plain,(
% 4.69/0.99    k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,sK0)),
% 4.69/0.99    inference(forward_demodulation,[],[f2637,f1086])).
% 4.69/0.99  fof(f1086,plain,(
% 4.69/0.99    ( ! [X0] : (k4_xboole_0(sK1,X0) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(X0,sK1))))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f1085,f20])).
% 4.69/0.99  fof(f1085,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(X0,sK1)))) = k5_xboole_0(sK1,k3_xboole_0(sK1,X0))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f1084,f29])).
% 4.69/0.99  fof(f1084,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(X0,sK1)))) = k5_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK1,X0))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f1078,f55])).
% 4.69/0.99  fof(f1078,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(X0,sK1)))) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,X0)))) )),
% 4.69/0.99    inference(superposition,[],[f162,f1055])).
% 4.69/0.99  fof(f2637,plain,(
% 4.69/0.99    k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(k2_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1))))),
% 4.69/0.99    inference(superposition,[],[f1083,f2505])).
% 4.69/0.99  fof(f1821,plain,(
% 4.69/0.99    k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k2_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(backward_demodulation,[],[f1339,f1806])).
% 4.69/0.99  fof(f4363,plain,(
% 4.69/0.99    k2_xboole_0(sK1,sK0) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,sK0)))),
% 4.69/0.99    inference(backward_demodulation,[],[f2978,f4358])).
% 4.69/0.99  fof(f4358,plain,(
% 4.69/0.99    k2_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k3_xboole_0(sK0,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f4341,f1806])).
% 4.69/0.99  fof(f4341,plain,(
% 4.69/0.99    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k3_xboole_0(sK0,sK0))),
% 4.69/0.99    inference(backward_demodulation,[],[f3207,f4316])).
% 4.69/0.99  fof(f4316,plain,(
% 4.69/0.99    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f4314,f1795])).
% 4.69/0.99  fof(f4314,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(backward_demodulation,[],[f4313,f4294])).
% 4.69/0.99  fof(f4294,plain,(
% 4.69/0.99    k5_xboole_0(sK1,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(superposition,[],[f31,f3962])).
% 4.69/0.99  fof(f3962,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK0,sK1)),
% 4.69/0.99    inference(forward_demodulation,[],[f3961,f2756])).
% 4.69/0.99  fof(f2756,plain,(
% 4.69/0.99    k4_xboole_0(sK0,sK1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2755,f1693])).
% 4.69/0.99  fof(f2755,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2655,f23])).
% 4.69/0.99  fof(f2655,plain,(
% 4.69/0.99    k4_xboole_0(k3_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(superposition,[],[f36,f2505])).
% 4.69/0.99  fof(f3961,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f3960,f3940])).
% 4.69/0.99  fof(f3940,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f3939,f63])).
% 4.69/0.99  fof(f3939,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f3913,f633])).
% 4.69/0.99  fof(f3913,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k2_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(superposition,[],[f54,f3900])).
% 4.69/0.99  fof(f3900,plain,(
% 4.69/0.99    k5_xboole_0(sK1,sK1) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f3899,f1965])).
% 4.69/0.99  fof(f3899,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k4_xboole_0(sK1,sK0)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f3898,f2750])).
% 4.69/0.99  fof(f2750,plain,(
% 4.69/0.99    ( ! [X7] : (k3_xboole_0(sK0,k4_xboole_0(sK1,X7)) = k3_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK1,X7)))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f2651,f23])).
% 4.69/0.99  fof(f2651,plain,(
% 4.69/0.99    ( ! [X7] : (k4_xboole_0(k3_xboole_0(sK0,sK1),X7) = k3_xboole_0(sK1,k4_xboole_0(k3_xboole_0(sK0,sK1),X7))) )),
% 4.69/0.99    inference(superposition,[],[f23,f2505])).
% 4.69/0.99  fof(f3898,plain,(
% 4.69/0.99    k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k3_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),
% 4.69/0.99    inference(forward_demodulation,[],[f3897,f23])).
% 4.69/0.99  fof(f3897,plain,(
% 4.69/0.99    k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k3_xboole_0(sK1,k4_xboole_0(k3_xboole_0(sK0,sK1),sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f3896,f130])).
% 4.69/0.99  fof(f3896,plain,(
% 4.69/0.99    k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k3_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f3895,f18])).
% 4.69/0.99  fof(f3895,plain,(
% 4.69/0.99    k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0)) = k3_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f3876,f3894])).
% 4.69/0.99  fof(f3894,plain,(
% 4.69/0.99    k2_xboole_0(sK1,sK0) = k2_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f3875,f2748])).
% 4.69/0.99  fof(f2748,plain,(
% 4.69/0.99    k2_xboole_0(sK1,sK0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2648,f1806])).
% 4.69/0.99  fof(f2648,plain,(
% 4.69/0.99    k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(superposition,[],[f1312,f2505])).
% 4.69/0.99  fof(f1312,plain,(
% 4.69/0.99    ( ! [X28,X27] : (k5_xboole_0(k4_xboole_0(sK1,X27),k3_xboole_0(X28,k3_xboole_0(X27,sK1))) = k4_xboole_0(sK1,k4_xboole_0(X27,X28))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f1311,f1128])).
% 4.69/0.99  fof(f1311,plain,(
% 4.69/0.99    ( ! [X28,X27] : (k5_xboole_0(k4_xboole_0(sK1,X27),k3_xboole_0(X28,k3_xboole_0(X27,sK1))) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(X27,k4_xboole_0(sK1,X28))))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f1281,f23])).
% 4.69/0.99  fof(f1281,plain,(
% 4.69/0.99    ( ! [X28,X27] : (k5_xboole_0(k4_xboole_0(sK1,X27),k3_xboole_0(X28,k3_xboole_0(X27,sK1))) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(k3_xboole_0(X27,sK1),X28)))) )),
% 4.69/0.99    inference(superposition,[],[f1149,f36])).
% 4.69/0.99  fof(f3875,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)) = k2_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(superposition,[],[f19,f2774])).
% 4.69/0.99  fof(f2774,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f2773,f2679])).
% 4.69/0.99  fof(f2773,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f2663,f2654])).
% 4.69/0.99  fof(f2654,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(superposition,[],[f31,f2505])).
% 4.69/0.99  fof(f2663,plain,(
% 4.69/0.99    k4_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))) = k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(superposition,[],[f659,f2505])).
% 4.69/0.99  fof(f3876,plain,(
% 4.69/0.99    k3_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(superposition,[],[f40,f2774])).
% 4.69/0.99  fof(f40,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 4.69/0.99    inference(superposition,[],[f21,f19])).
% 4.69/0.99  fof(f3960,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),
% 4.69/0.99    inference(backward_demodulation,[],[f3908,f3959])).
% 4.69/0.99  fof(f3959,plain,(
% 4.69/0.99    k4_xboole_0(sK1,sK0) = k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)),
% 4.69/0.99    inference(forward_demodulation,[],[f3926,f3234])).
% 4.69/0.99  fof(f3234,plain,(
% 4.69/0.99    k4_xboole_0(sK1,sK0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f3228,f1126])).
% 4.69/0.99  fof(f3228,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1)) = k5_xboole_0(sK0,k5_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(superposition,[],[f1149,f2363])).
% 4.69/0.99  fof(f2363,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2362,f18])).
% 4.69/0.99  fof(f2362,plain,(
% 4.69/0.99    k3_xboole_0(sK1,sK0) = k5_xboole_0(k3_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2268,f21])).
% 4.69/0.99  fof(f2268,plain,(
% 4.69/0.99    k5_xboole_0(k3_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1)) = k5_xboole_0(k5_xboole_0(sK1,sK0),k2_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(superposition,[],[f58,f2007])).
% 4.69/0.99  fof(f3926,plain,(
% 4.69/0.99    k4_xboole_0(k4_xboole_0(sK1,sK0),sK0) = k5_xboole_0(k4_xboole_0(sK1,sK0),k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(superposition,[],[f36,f3900])).
% 4.69/0.99  fof(f3908,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)))),
% 4.69/0.99    inference(backward_demodulation,[],[f3835,f3900])).
% 4.69/0.99  fof(f3835,plain,(
% 4.69/0.99    k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK0),sK0))) = k3_xboole_0(sK0,k3_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),
% 4.69/0.99    inference(forward_demodulation,[],[f3834,f130])).
% 4.69/0.99  fof(f3834,plain,(
% 4.69/0.99    k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK0),sK0))) = k3_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK0,sK0)))),
% 4.69/0.99    inference(forward_demodulation,[],[f3833,f3529])).
% 4.69/0.99  fof(f3529,plain,(
% 4.69/0.99    ( ! [X14] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,sK0))) = k3_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(X14,sK0)))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f3527,f639])).
% 4.69/0.99  fof(f639,plain,(
% 4.69/0.99    ( ! [X6,X8,X7] : (k3_xboole_0(X6,k3_xboole_0(X7,k4_xboole_0(X8,X6))) = k5_xboole_0(k2_xboole_0(X6,k3_xboole_0(X7,X8)),k2_xboole_0(X6,k3_xboole_0(X7,k4_xboole_0(X8,X6))))) )),
% 4.69/0.99    inference(superposition,[],[f21,f54])).
% 4.69/0.99  fof(f3527,plain,(
% 4.69/0.99    ( ! [X14] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,sK0))) = k5_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,X14)),k2_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(X14,sK0))))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f3506,f3514])).
% 4.69/0.99  fof(f3514,plain,(
% 4.69/0.99    ( ! [X2,X3] : (k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X2,k4_xboole_0(sK1,X3))) = k2_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(X2,X3)))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f749,f3496])).
% 4.69/0.99  fof(f3496,plain,(
% 4.69/0.99    ( ! [X1] : (k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X1)) = k2_xboole_0(sK0,k3_xboole_0(sK1,X1))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f742,f3494])).
% 4.69/0.99  fof(f3494,plain,(
% 4.69/0.99    ( ! [X15] : (k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X15,sK1)) = k2_xboole_0(sK0,k3_xboole_0(sK1,X15))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f3493,f54])).
% 4.69/0.99  fof(f3493,plain,(
% 4.69/0.99    ( ! [X15] : (k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X15,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(X15,sK0)))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f2827,f3396])).
% 4.69/0.99  fof(f3396,plain,(
% 4.69/0.99    ( ! [X33,X32] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X32,k4_xboole_0(sK1,X33))) = k5_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(X32,X33)))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f181,f3367])).
% 4.69/0.99  fof(f3367,plain,(
% 4.69/0.99    ( ! [X8] : (k3_xboole_0(sK1,X8) = k5_xboole_0(sK1,k4_xboole_0(sK1,X8))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f3350,f20])).
% 4.69/0.99  fof(f3350,plain,(
% 4.69/0.99    ( ! [X8] : (k3_xboole_0(sK1,X8) = k5_xboole_0(sK1,k5_xboole_0(sK1,k3_xboole_0(sK1,X8)))) )),
% 4.69/0.99    inference(superposition,[],[f2560,f62])).
% 4.69/0.99  fof(f2560,plain,(
% 4.69/0.99    ( ! [X1] : (k5_xboole_0(sK1,X1) = k5_xboole_0(sK1,k5_xboole_0(sK1,k5_xboole_0(sK1,X1)))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f2502,f24])).
% 4.69/0.99  fof(f2502,plain,(
% 4.69/0.99    ( ! [X1] : (k5_xboole_0(sK1,X1) = k5_xboole_0(sK1,k5_xboole_0(k5_xboole_0(sK1,sK1),X1))) )),
% 4.69/0.99    inference(superposition,[],[f24,f2494])).
% 4.69/0.99  fof(f181,plain,(
% 4.69/0.99    ( ! [X33,X32] : (k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X32,X33)))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X32,k4_xboole_0(sK1,X33)))) )),
% 4.69/0.99    inference(superposition,[],[f86,f130])).
% 4.69/0.99  fof(f2827,plain,(
% 4.69/0.99    ( ! [X15] : (k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X15,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X15,k4_xboole_0(sK1,sK0)))) )),
% 4.69/0.99    inference(superposition,[],[f54,f2679])).
% 4.69/0.99  fof(f742,plain,(
% 4.69/0.99    ( ! [X1] : (k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X1)) = k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X1,sK1))) )),
% 4.69/0.99    inference(superposition,[],[f635,f634])).
% 4.69/0.99  fof(f634,plain,(
% 4.69/0.99    ( ! [X5] : (k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X5,k3_xboole_0(sK0,sK1))))) = k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X5))) )),
% 4.69/0.99    inference(superposition,[],[f54,f86])).
% 4.69/0.99  fof(f635,plain,(
% 4.69/0.99    ( ! [X6] : (k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,k4_xboole_0(X6,k3_xboole_0(sK0,sK1))))) = k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X6,sK1))) )),
% 4.69/0.99    inference(superposition,[],[f54,f181])).
% 4.69/0.99  fof(f749,plain,(
% 4.69/0.99    ( ! [X2,X3] : (k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,k4_xboole_0(X2,X3))) = k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X2,k4_xboole_0(sK1,X3)))) )),
% 4.69/0.99    inference(superposition,[],[f742,f165])).
% 4.69/0.99  fof(f165,plain,(
% 4.69/0.99    ( ! [X6,X8,X7] : (k3_xboole_0(k4_xboole_0(X7,X8),X6) = k3_xboole_0(X7,k4_xboole_0(X6,X8))) )),
% 4.69/0.99    inference(superposition,[],[f130,f18])).
% 4.69/0.99  fof(f3506,plain,(
% 4.69/0.99    ( ! [X14] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,sK0))) = k5_xboole_0(k2_xboole_0(sK0,k3_xboole_0(sK1,X14)),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,sK0))))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f2681,f3496])).
% 4.69/0.99  fof(f2681,plain,(
% 4.69/0.99    ( ! [X14] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,sK0))) = k5_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X14)),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,sK0))))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f1430,f2679])).
% 4.69/0.99  fof(f1430,plain,(
% 4.69/0.99    ( ! [X14] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) = k5_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X14)),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X14,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f1406,f23])).
% 4.69/0.99  fof(f1406,plain,(
% 4.69/0.99    ( ! [X14] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(X14,sK1),k3_xboole_0(sK0,sK1))) = k5_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X14)),k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(X14,sK1),k3_xboole_0(sK0,sK1))))) )),
% 4.69/0.99    inference(superposition,[],[f40,f742])).
% 4.69/0.99  fof(f3833,plain,(
% 4.69/0.99    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK0))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK0),sK0)))),
% 4.69/0.99    inference(forward_demodulation,[],[f3832,f2679])).
% 4.69/0.99  fof(f3832,plain,(
% 4.69/0.99    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)),sK0)))),
% 4.69/0.99    inference(forward_demodulation,[],[f3831,f661])).
% 4.69/0.99  fof(f661,plain,(
% 4.69/0.99    ( ! [X6,X4,X5] : (k4_xboole_0(X4,k4_xboole_0(k4_xboole_0(X5,X6),X4)) = k2_xboole_0(X4,k3_xboole_0(X5,k4_xboole_0(X4,X6)))) )),
% 4.69/0.99    inference(superposition,[],[f633,f130])).
% 4.69/0.99  fof(f3831,plain,(
% 4.69/0.99    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,k3_xboole_0(sK1,k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))),
% 4.69/0.99    inference(forward_demodulation,[],[f3830,f3514])).
% 4.69/0.99  fof(f3830,plain,(
% 4.69/0.99    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 4.69/0.99    inference(forward_demodulation,[],[f3821,f23])).
% 4.69/0.99  fof(f3821,plain,(
% 4.69/0.99    k3_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))))),
% 4.69/0.99    inference(superposition,[],[f40,f2654])).
% 4.69/0.99  fof(f4313,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f4310,f2524])).
% 4.69/0.99  fof(f2524,plain,(
% 4.69/0.99    k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(backward_demodulation,[],[f1844,f2523])).
% 4.69/0.99  fof(f2523,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2510,f20])).
% 4.69/0.99  fof(f2510,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(backward_demodulation,[],[f2357,f2505])).
% 4.69/0.99  fof(f2357,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),
% 4.69/0.99    inference(backward_demodulation,[],[f2147,f2354])).
% 4.69/0.99  fof(f2147,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))))),
% 4.69/0.99    inference(forward_demodulation,[],[f2146,f1693])).
% 4.69/0.99  fof(f2146,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k3_xboole_0(sK0,k4_xboole_0(sK1,sK1))) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))))),
% 4.69/0.99    inference(forward_demodulation,[],[f2145,f23])).
% 4.69/0.99  fof(f2145,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) = k3_xboole_0(sK0,k4_xboole_0(k3_xboole_0(sK0,sK1),sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2144,f130])).
% 4.69/0.99  fof(f2144,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0)))) = k3_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2143,f18])).
% 4.69/0.99  fof(f2143,plain,(
% 4.69/0.99    k3_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,sK0))))),
% 4.69/0.99    inference(forward_demodulation,[],[f2137,f87])).
% 4.69/0.99  fof(f2137,plain,(
% 4.69/0.99    k3_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(superposition,[],[f62,f1945])).
% 4.69/0.99  fof(f1945,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(resolution,[],[f1942,f22])).
% 4.69/0.99  fof(f1942,plain,(
% 4.69/0.99    r1_tarski(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(superposition,[],[f1853,f1693])).
% 4.69/0.99  fof(f1853,plain,(
% 4.69/0.99    ( ! [X0] : (r1_tarski(k3_xboole_0(sK0,k4_xboole_0(X0,sK1)),k3_xboole_0(sK0,sK1))) )),
% 4.69/0.99    inference(superposition,[],[f1776,f130])).
% 4.69/0.99  fof(f1776,plain,(
% 4.69/0.99    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f1749,f18])).
% 4.69/0.99  fof(f1749,plain,(
% 4.69/0.99    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k4_xboole_0(sK0,sK1)),k3_xboole_0(sK1,sK0))) )),
% 4.69/0.99    inference(superposition,[],[f196,f1693])).
% 4.69/0.99  fof(f196,plain,(
% 4.69/0.99    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_xboole_0(X3,k3_xboole_0(X1,k4_xboole_0(X0,X2))),k3_xboole_0(X0,X1))) )),
% 4.69/0.99    inference(superposition,[],[f171,f52])).
% 4.69/0.99  fof(f171,plain,(
% 4.69/0.99    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X1,k4_xboole_0(X0,X2)),X0)) )),
% 4.69/0.99    inference(superposition,[],[f17,f130])).
% 4.69/0.99  fof(f1844,plain,(
% 4.69/0.99    k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f1843,f179])).
% 4.69/0.99  fof(f179,plain,(
% 4.69/0.99    ( ! [X26,X27,X25] : (k4_xboole_0(k4_xboole_0(X26,X27),X25) = k5_xboole_0(k4_xboole_0(X26,X27),k3_xboole_0(X26,k4_xboole_0(X25,X27)))) )),
% 4.69/0.99    inference(superposition,[],[f36,f130])).
% 4.69/0.99  fof(f1843,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f1842,f23])).
% 4.69/0.99  fof(f1842,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f1808,f837])).
% 4.69/0.99  fof(f837,plain,(
% 4.69/0.99    ( ! [X8] : (k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(X8,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,X8))))) )),
% 4.69/0.99    inference(superposition,[],[f56,f85])).
% 4.69/0.99  fof(f1808,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k3_xboole_0(sK0,sK1),sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(sK1,k2_xboole_0(sK1,sK0))))),
% 4.69/0.99    inference(superposition,[],[f837,f1775])).
% 4.69/0.99  fof(f4310,plain,(
% 4.69/0.99    k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) = k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)))),
% 4.69/0.99    inference(backward_demodulation,[],[f2010,f4291])).
% 4.69/0.99  fof(f4291,plain,(
% 4.69/0.99    ( ! [X0] : (k4_xboole_0(k4_xboole_0(sK0,sK1),X0) = k3_xboole_0(sK0,k4_xboole_0(k5_xboole_0(sK1,sK1),X0))) )),
% 4.69/0.99    inference(superposition,[],[f23,f3962])).
% 4.69/0.99  fof(f2010,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1))) = k3_xboole_0(sK0,k4_xboole_0(k5_xboole_0(sK1,sK1),sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2004,f165])).
% 4.69/0.99  fof(f2004,plain,(
% 4.69/0.99    k3_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(sK1,sK1)))),
% 4.69/0.99    inference(superposition,[],[f21,f1795])).
% 4.69/0.99  fof(f3207,plain,(
% 4.69/0.99    k4_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))) = k2_xboole_0(sK1,k3_xboole_0(sK0,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f3206,f2973])).
% 4.69/0.99  fof(f2973,plain,(
% 4.69/0.99    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k2_xboole_0(sK1,k3_xboole_0(sK0,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f2948,f54])).
% 4.69/0.99  fof(f2948,plain,(
% 4.69/0.99    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(superposition,[],[f19,f2524])).
% 4.69/0.99  fof(f3206,plain,(
% 4.69/0.99    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f3154,f2524])).
% 4.69/0.99  fof(f3154,plain,(
% 4.69/0.99    k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k4_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),sK1))),
% 4.69/0.99    inference(superposition,[],[f633,f3112])).
% 4.69/0.99  fof(f3112,plain,(
% 4.69/0.99    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK1,k4_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f3111,f3104])).
% 4.69/0.99  fof(f3104,plain,(
% 4.69/0.99    k4_xboole_0(sK0,sK1) = k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,k3_xboole_0(sK0,sK0)))),
% 4.69/0.99    inference(forward_demodulation,[],[f3103,f1693])).
% 4.69/0.99  fof(f3103,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,k3_xboole_0(sK0,sK0)))),
% 4.69/0.99    inference(forward_demodulation,[],[f3087,f130])).
% 4.69/0.99  fof(f3087,plain,(
% 4.69/0.99    k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,k3_xboole_0(sK0,sK0)))),
% 4.69/0.99    inference(superposition,[],[f40,f2973])).
% 4.69/0.99  fof(f3111,plain,(
% 4.69/0.99    k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k2_xboole_0(sK1,sK0),k2_xboole_0(sK1,k3_xboole_0(sK0,sK0)))),
% 4.69/0.99    inference(forward_demodulation,[],[f3091,f19])).
% 4.69/0.99  fof(f3091,plain,(
% 4.69/0.99    k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK0,sK1)),k2_xboole_0(sK1,k3_xboole_0(sK0,sK0)))),
% 4.69/0.99    inference(superposition,[],[f21,f2973])).
% 4.69/0.99  fof(f2978,plain,(
% 4.69/0.99    k2_xboole_0(sK1,sK0) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k3_xboole_0(sK0,sK0))))),
% 4.69/0.99    inference(backward_demodulation,[],[f1817,f2973])).
% 4.69/0.99  fof(f1817,plain,(
% 4.69/0.99    k2_xboole_0(sK1,sK0) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))))),
% 4.69/0.99    inference(backward_demodulation,[],[f1093,f1806])).
% 4.69/0.99  fof(f1826,plain,(
% 4.69/0.99    k5_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK1,sK0))) = k3_xboole_0(sK0,k4_xboole_0(k2_xboole_0(sK1,sK0),sK1))),
% 4.69/0.99    inference(backward_demodulation,[],[f1792,f1806])).
% 4.69/0.99  fof(f1792,plain,(
% 4.69/0.99    k5_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)),sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f1791,f231])).
% 4.69/0.99  fof(f231,plain,(
% 4.69/0.99    ( ! [X12,X10,X11,X9] : (k3_xboole_0(X11,k4_xboole_0(k4_xboole_0(X9,X10),X12)) = k3_xboole_0(X9,k4_xboole_0(k4_xboole_0(X11,X12),X10))) )),
% 4.69/0.99    inference(superposition,[],[f165,f130])).
% 4.69/0.99  fof(f1791,plain,(
% 4.69/0.99    k5_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1)))) = k3_xboole_0(sK1,k4_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(forward_demodulation,[],[f1788,f130])).
% 4.69/0.99  fof(f1788,plain,(
% 4.69/0.99    k3_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))) = k5_xboole_0(sK1,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,k4_xboole_0(sK0,sK1))))),
% 4.69/0.99    inference(superposition,[],[f40,f1748])).
% 4.69/0.99  fof(f3845,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(backward_demodulation,[],[f1753,f3844])).
% 4.69/0.99  fof(f3844,plain,(
% 4.69/0.99    k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f3843,f18])).
% 4.69/0.99  fof(f3843,plain,(
% 4.69/0.99    k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k3_xboole_0(sK0,k3_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f3842,f3522])).
% 4.69/0.99  fof(f3522,plain,(
% 4.69/0.99    ( ! [X4] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X4,sK1)) = k3_xboole_0(sK0,k3_xboole_0(sK1,X4))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f3495,f3521])).
% 4.69/0.99  fof(f3521,plain,(
% 4.69/0.99    ( ! [X3] : (k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,X3),k2_xboole_0(sK0,k3_xboole_0(sK1,X3))))) = k3_xboole_0(sK0,k3_xboole_0(sK1,X3))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f3504,f3519])).
% 4.69/0.99  fof(f3519,plain,(
% 4.69/0.99    ( ! [X2] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X2)) = k3_xboole_0(sK0,k3_xboole_0(sK1,X2))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f3508,f21])).
% 4.69/0.99  fof(f3508,plain,(
% 4.69/0.99    ( ! [X2] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK1,X2)),k2_xboole_0(sK0,k3_xboole_0(sK1,X2)))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f3370,f3496])).
% 4.69/0.99  fof(f3370,plain,(
% 4.69/0.99    ( ! [X2] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X2)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK1,X2)),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X2)))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f110,f3367])).
% 4.69/0.99  fof(f110,plain,(
% 4.69/0.99    ( ! [X2] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X2)) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,X2))),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X2)))) )),
% 4.69/0.99    inference(superposition,[],[f21,f86])).
% 4.69/0.99  fof(f3504,plain,(
% 4.69/0.99    ( ! [X3] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X3)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,X3),k2_xboole_0(sK0,k3_xboole_0(sK1,X3)))))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f487,f3496])).
% 4.69/0.99  fof(f487,plain,(
% 4.69/0.99    ( ! [X3] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X3)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,X3),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK1,X3)))))) )),
% 4.69/0.99    inference(superposition,[],[f114,f62])).
% 4.69/0.99  fof(f114,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK1,X0),X1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,X0),X1)))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f113,f24])).
% 4.69/0.99  fof(f113,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK1,X0),X1)) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK1,X0)),X1))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f109,f24])).
% 4.69/0.99  fof(f109,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK1,X0),X1)) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,X0))),X1)) )),
% 4.69/0.99    inference(superposition,[],[f24,f86])).
% 4.69/0.99  fof(f3495,plain,(
% 4.69/0.99    ( ! [X4] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X4,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,X4),k2_xboole_0(sK0,k3_xboole_0(sK1,X4)))))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f524,f3494])).
% 4.69/0.99  fof(f524,plain,(
% 4.69/0.99    ( ! [X4] : (k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X4,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,X4),k2_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X4,sK1)))))) )),
% 4.69/0.99    inference(superposition,[],[f124,f62])).
% 4.69/0.99  fof(f124,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(k4_xboole_0(sK1,X0),X1))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(X0,sK1),X1))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f123,f24])).
% 4.69/0.99  fof(f123,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK1,k4_xboole_0(sK1,X0)),X1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(X0,sK1),X1))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f119,f24])).
% 4.69/0.99  fof(f119,plain,(
% 4.69/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k4_xboole_0(sK1,X0))),X1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(X0,sK1),X1))) )),
% 4.69/0.99    inference(superposition,[],[f24,f87])).
% 4.69/0.99  fof(f3842,plain,(
% 4.69/0.99    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f3841,f2536])).
% 4.69/0.99  fof(f2536,plain,(
% 4.69/0.99    k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2535,f1753])).
% 4.69/0.99  fof(f2535,plain,(
% 4.69/0.99    k5_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f2511,f20])).
% 4.69/0.99  fof(f2511,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))),
% 4.69/0.99    inference(backward_demodulation,[],[f2383,f2505])).
% 4.69/0.99  fof(f2383,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(sK1,k3_xboole_0(sK0,sK1))))),
% 4.69/0.99    inference(superposition,[],[f833,f2354])).
% 4.69/0.99  fof(f3841,plain,(
% 4.69/0.99    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f3840,f36])).
% 4.69/0.99  fof(f3840,plain,(
% 4.69/0.99    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(sK0,k3_xboole_0(sK1,sK0)),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f3823,f3369])).
% 4.69/0.99  fof(f3369,plain,(
% 4.69/0.99    ( ! [X2] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X2,sK1)) = k5_xboole_0(sK0,k3_xboole_0(sK1,X2))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f87,f3367])).
% 4.69/0.99  fof(f3823,plain,(
% 4.69/0.99    k3_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) = k5_xboole_0(k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(superposition,[],[f21,f2654])).
% 4.69/0.99  fof(f1753,plain,(
% 4.69/0.99    k4_xboole_0(sK0,k4_xboole_0(sK1,sK1)) = k5_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(superposition,[],[f20,f1693])).
% 4.69/0.99  fof(f3850,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k3_xboole_0(sK0,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(backward_demodulation,[],[f2536,f3844])).
% 4.69/0.99  fof(f5311,plain,(
% 4.69/0.99    k2_xboole_0(k4_xboole_0(sK0,sK1),sK0) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(superposition,[],[f19,f4657])).
% 4.69/0.99  fof(f4657,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f4613,f4629])).
% 4.69/0.99  fof(f4613,plain,(
% 4.69/0.99    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(backward_demodulation,[],[f4021,f4573])).
% 4.69/0.99  fof(f4021,plain,(
% 4.69/0.99    k4_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k3_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f3996,f3850])).
% 4.69/0.99  fof(f3996,plain,(
% 4.69/0.99    k4_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(backward_demodulation,[],[f881,f3994])).
% 4.69/0.99  fof(f3994,plain,(
% 4.69/0.99    k3_xboole_0(sK0,sK1) = k2_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f3993,f3940])).
% 4.69/0.99  fof(f3993,plain,(
% 4.69/0.99    k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f3933,f3959])).
% 4.69/0.99  fof(f3933,plain,(
% 4.69/0.99    k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK0),sK0))),
% 4.69/0.99    inference(superposition,[],[f633,f3900])).
% 4.69/0.99  fof(f881,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,k5_xboole_0(sK1,sK1))) = k4_xboole_0(sK0,k5_xboole_0(sK1,sK1))),
% 4.69/0.99    inference(forward_demodulation,[],[f847,f20])).
% 4.69/0.99  fof(f847,plain,(
% 4.69/0.99    k5_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(sK0,k5_xboole_0(sK1,sK1))) = k5_xboole_0(sK0,k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)))),
% 4.69/0.99    inference(superposition,[],[f56,f76])).
% 4.69/0.99  fof(f76,plain,(
% 4.69/0.99    k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)))),
% 4.69/0.99    inference(superposition,[],[f21,f63])).
% 4.69/0.99  fof(f4671,plain,(
% 4.69/0.99    ( ! [X1] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X1)) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,sK1),X1))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f3859,f4668])).
% 4.69/0.99  fof(f4668,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_xboole_0(sK0,sK1),X0)) )),
% 4.69/0.99    inference(forward_demodulation,[],[f4667,f1693])).
% 4.69/0.99  fof(f4667,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k3_xboole_0(sK0,k4_xboole_0(sK1,sK1)),X0)) )),
% 4.69/0.99    inference(forward_demodulation,[],[f4618,f130])).
% 4.69/0.99  fof(f4618,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k3_xboole_0(sK1,k4_xboole_0(sK0,sK1)),X0)) )),
% 4.69/0.99    inference(backward_demodulation,[],[f4269,f4573])).
% 4.69/0.99  fof(f4269,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k3_xboole_0(sK1,k5_xboole_0(sK1,sK1)),X0)) )),
% 4.69/0.99    inference(forward_demodulation,[],[f4268,f18])).
% 4.69/0.99  fof(f4268,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK1),sK1),X0)) )),
% 4.69/0.99    inference(forward_demodulation,[],[f4267,f2494])).
% 4.69/0.99  fof(f4267,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK1),sK1),X0) = k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK1,X0))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f4263,f24])).
% 4.69/0.99  fof(f4263,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(k3_xboole_0(k5_xboole_0(sK1,sK1),sK1),X0) = k5_xboole_0(k5_xboole_0(k5_xboole_0(sK1,sK1),sK1),k5_xboole_0(sK1,X0))) )),
% 4.69/0.99    inference(superposition,[],[f58,f3916])).
% 4.69/0.99  fof(f3916,plain,(
% 4.69/0.99    sK1 = k2_xboole_0(k5_xboole_0(sK1,sK1),sK1)),
% 4.69/0.99    inference(superposition,[],[f177,f3900])).
% 4.69/0.99  fof(f3859,plain,(
% 4.69/0.99    ( ! [X1] : (k5_xboole_0(k4_xboole_0(sK0,sK1),X1) = k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k3_xboole_0(sK0,sK1),X1))) )),
% 4.69/0.99    inference(superposition,[],[f24,f2756])).
% 4.69/0.99  fof(f5332,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(sK1,k5_xboole_0(sK1,X0))) = k5_xboole_0(sK0,X0)) )),
% 4.69/0.99    inference(backward_demodulation,[],[f77,f5331])).
% 4.69/0.99  fof(f6739,plain,(
% 4.69/0.99    ( ! [X16] : (k4_xboole_0(sK0,k4_xboole_0(sK0,X16)) = k5_xboole_0(sK0,k4_xboole_0(sK0,X16))) )),
% 4.69/0.99    inference(superposition,[],[f20,f5883])).
% 4.69/0.99  fof(f5883,plain,(
% 4.69/0.99    ( ! [X0] : (k4_xboole_0(sK0,X0) = k3_xboole_0(sK0,k4_xboole_0(sK0,X0))) )),
% 4.69/0.99    inference(superposition,[],[f23,f5486])).
% 4.69/0.99  fof(f5486,plain,(
% 4.69/0.99    sK0 = k3_xboole_0(sK0,sK0)),
% 4.69/0.99    inference(backward_demodulation,[],[f4629,f5331])).
% 4.69/0.99  fof(f6756,plain,(
% 4.69/0.99    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f5997,f6739])).
% 4.69/0.99  fof(f5997,plain,(
% 4.69/0.99    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k5_xboole_0(sK0,k4_xboole_0(sK0,X0))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f5996,f5813])).
% 4.69/0.99  fof(f5813,plain,(
% 4.69/0.99    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k2_xboole_0(k4_xboole_0(sK0,sK0),k3_xboole_0(X0,sK0))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f5812,f5602])).
% 4.69/0.99  fof(f5602,plain,(
% 4.69/0.99    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,sK0)),
% 4.69/0.99    inference(backward_demodulation,[],[f4585,f5590])).
% 4.69/0.99  fof(f5590,plain,(
% 4.69/0.99    ( ! [X3] : (k3_xboole_0(sK0,k4_xboole_0(sK1,X3)) = k4_xboole_0(sK0,X3)) )),
% 4.69/0.99    inference(forward_demodulation,[],[f5454,f20])).
% 4.69/0.99  fof(f5454,plain,(
% 4.69/0.99    ( ! [X3] : (k3_xboole_0(sK0,k4_xboole_0(sK1,X3)) = k5_xboole_0(sK0,k3_xboole_0(sK0,X3))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f4058,f5331])).
% 4.69/0.99  fof(f4058,plain,(
% 4.69/0.99    ( ! [X3] : (k3_xboole_0(sK0,k4_xboole_0(sK1,X3)) = k5_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK1),X3))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f4057,f23])).
% 4.69/0.99  fof(f4057,plain,(
% 4.69/0.99    ( ! [X3] : (k4_xboole_0(k3_xboole_0(sK0,sK1),X3) = k5_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK1),X3))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f4056,f20])).
% 4.69/0.99  fof(f4056,plain,(
% 4.69/0.99    ( ! [X3] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),X3)) = k5_xboole_0(sK0,k3_xboole_0(k3_xboole_0(sK0,sK1),X3))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f4010,f853])).
% 4.69/0.99  fof(f853,plain,(
% 4.69/0.99    ( ! [X35,X36,X34] : (k5_xboole_0(k4_xboole_0(X34,X35),k5_xboole_0(X36,k2_xboole_0(k3_xboole_0(X34,X35),X36))) = k5_xboole_0(X34,k3_xboole_0(k3_xboole_0(X34,X35),X36))) )),
% 4.69/0.99    inference(superposition,[],[f56,f62])).
% 4.69/0.99  fof(f4010,plain,(
% 4.69/0.99    ( ! [X3] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k3_xboole_0(sK0,sK1),X3)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(X3,k2_xboole_0(k3_xboole_0(sK0,sK1),X3)))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f3969,f3994])).
% 4.69/0.99  fof(f3969,plain,(
% 4.69/0.99    ( ! [X3] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)),X3)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k5_xboole_0(X3,k2_xboole_0(k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)),X3)))) )),
% 4.69/0.99    inference(backward_demodulation,[],[f428,f3962])).
% 4.69/0.99  fof(f428,plain,(
% 4.69/0.99    ( ! [X3] : (k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k5_xboole_0(X3,k2_xboole_0(k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)),X3))) = k5_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)),X3))) )),
% 4.69/0.99    inference(superposition,[],[f98,f62])).
% 4.69/0.99  fof(f98,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(k2_xboole_0(sK0,k5_xboole_0(sK1,sK1)),X0)) = k5_xboole_0(k3_xboole_0(sK0,k5_xboole_0(sK1,sK1)),X0)) )),
% 4.69/0.99    inference(superposition,[],[f24,f76])).
% 4.69/0.99  fof(f4585,plain,(
% 4.69/0.99    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 4.69/0.99    inference(backward_demodulation,[],[f3900,f4573])).
% 4.69/0.99  fof(f5812,plain,(
% 4.69/0.99    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK1,X0)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(X0,sK0))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f5313,f886])).
% 4.69/0.99  fof(f886,plain,(
% 4.69/0.99    ( ! [X28,X29,X27] : (k5_xboole_0(k4_xboole_0(X27,X28),k3_xboole_0(X29,k3_xboole_0(X27,X28))) = k4_xboole_0(X27,k4_xboole_0(X28,X29))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f885,f20])).
% 4.69/0.99  fof(f885,plain,(
% 4.69/0.99    ( ! [X28,X29,X27] : (k5_xboole_0(k4_xboole_0(X27,X28),k3_xboole_0(X29,k3_xboole_0(X27,X28))) = k5_xboole_0(X27,k3_xboole_0(X27,k4_xboole_0(X28,X29)))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f851,f23])).
% 4.69/0.99  fof(f851,plain,(
% 4.69/0.99    ( ! [X28,X29,X27] : (k5_xboole_0(k4_xboole_0(X27,X28),k3_xboole_0(X29,k3_xboole_0(X27,X28))) = k5_xboole_0(X27,k4_xboole_0(k3_xboole_0(X27,X28),X29))) )),
% 4.69/0.99    inference(superposition,[],[f56,f36])).
% 4.69/0.99  fof(f5313,plain,(
% 4.69/0.99    ( ! [X0] : (k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(X0,sK0)) = k5_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(X0,k3_xboole_0(sK0,sK1)))) )),
% 4.69/0.99    inference(superposition,[],[f54,f4657])).
% 4.69/0.99  fof(f5996,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(sK0,k4_xboole_0(sK0,X0)) = k2_xboole_0(k4_xboole_0(sK0,sK0),k3_xboole_0(X0,sK0))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f5995,f36])).
% 4.69/0.99  fof(f5995,plain,(
% 4.69/0.99    ( ! [X0] : (k2_xboole_0(k4_xboole_0(sK0,sK0),k3_xboole_0(X0,sK0)) = k5_xboole_0(sK0,k5_xboole_0(sK0,k3_xboole_0(X0,sK0)))) )),
% 4.69/0.99    inference(forward_demodulation,[],[f5975,f5774])).
% 4.69/0.99  fof(f5774,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(sK0,X0)) = k5_xboole_0(k4_xboole_0(sK0,sK0),X0)) )),
% 4.69/0.99    inference(backward_demodulation,[],[f5690,f5498])).
% 4.69/0.99  fof(f5690,plain,(
% 4.69/0.99    ( ! [X0] : (k5_xboole_0(sK1,k5_xboole_0(sK1,X0)) = k5_xboole_0(k4_xboole_0(sK0,sK0),X0)) )),
% 4.69/0.99    inference(backward_demodulation,[],[f4668,f5602])).
% 4.69/0.99  fof(f5975,plain,(
% 4.69/0.99    ( ! [X0] : (k2_xboole_0(k4_xboole_0(sK0,sK0),k3_xboole_0(X0,sK0)) = k5_xboole_0(k4_xboole_0(sK0,sK0),k3_xboole_0(X0,sK0))) )),
% 4.69/0.99    inference(superposition,[],[f54,f5761])).
% 4.69/0.99  fof(f5761,plain,(
% 4.69/0.99    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK0))),
% 4.69/0.99    inference(forward_demodulation,[],[f5496,f5602])).
% 4.69/0.99  fof(f5496,plain,(
% 4.69/0.99    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 4.69/0.99    inference(backward_demodulation,[],[f4657,f5331])).
% 4.69/0.99  fof(f6576,plain,(
% 4.69/0.99    ( ! [X6] : (r1_tarski(k4_xboole_0(sK0,X6),sK1)) )),
% 4.69/0.99    inference(superposition,[],[f171,f5590])).
% 4.69/0.99  fof(f16,plain,(
% 4.69/0.99    ~r1_tarski(k3_xboole_0(sK0,sK2),sK1)),
% 4.69/0.99    inference(cnf_transformation,[],[f14])).
% 4.69/0.99  % SZS output end Proof for theBenchmark
% 4.69/0.99  % (6715)------------------------------
% 4.69/0.99  % (6715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.69/0.99  % (6715)Termination reason: Refutation
% 4.69/0.99  
% 4.69/0.99  % (6715)Memory used [KB]: 11001
% 4.69/0.99  % (6715)Time elapsed: 0.552 s
% 4.69/0.99  % (6715)------------------------------
% 4.69/0.99  % (6715)------------------------------
% 4.69/1.00  % (6698)Success in time 0.637 s
%------------------------------------------------------------------------------

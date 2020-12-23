%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:37 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 819 expanded)
%              Number of leaves         :   19 ( 231 expanded)
%              Depth                    :   23
%              Number of atoms          :  109 (1377 expanded)
%              Number of equality atoms :   88 ( 875 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f735,plain,(
    $false ),
    inference(subsumption_resolution,[],[f730,f204])).

fof(f204,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1 ),
    inference(backward_demodulation,[],[f100,f201])).

fof(f201,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = X4 ),
    inference(forward_demodulation,[],[f200,f68])).

fof(f68,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f56,f67])).

fof(f67,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(resolution,[],[f59,f61])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f41,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f56,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f29,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f200,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(backward_demodulation,[],[f156,f190])).

fof(f190,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f174,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f174,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f161,f68])).

fof(f161,plain,(
    ! [X8] : k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_xboole_0,X8),k1_xboole_0) ),
    inference(forward_demodulation,[],[f160,f67])).

fof(f160,plain,(
    ! [X8] : k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_xboole_0,X8),k5_xboole_0(k3_xboole_0(k1_xboole_0,X8),k3_xboole_0(k3_xboole_0(k1_xboole_0,X8),k3_xboole_0(k1_xboole_0,X8)))) ),
    inference(forward_demodulation,[],[f144,f69])).

fof(f69,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f68,f32])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f144,plain,(
    ! [X8] : k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_xboole_0,X8),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X8),k3_xboole_0(k3_xboole_0(k1_xboole_0,X8),k3_xboole_0(k1_xboole_0,X8))))) ),
    inference(superposition,[],[f65,f69])).

fof(f65,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))))) = X0 ),
    inference(backward_demodulation,[],[f64,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = X0 ),
    inference(forward_demodulation,[],[f58,f31])).

fof(f58,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))) = X0 ),
    inference(definition_unfolding,[],[f36,f48,f34])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f156,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f155,f67])).

fof(f155,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X4,k3_xboole_0(X4,X4)))) ),
    inference(forward_demodulation,[],[f154,f32])).

fof(f154,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X4),X4))) ),
    inference(forward_demodulation,[],[f153,f100])).

fof(f153,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = k5_xboole_0(X4,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X4),X4)),k3_xboole_0(X4,X4)))) ),
    inference(forward_demodulation,[],[f141,f88])).

fof(f88,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f43,f32])).

fof(f141,plain,(
    ! [X4] : k3_xboole_0(X4,X4) = k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X4),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X4),X4))))) ),
    inference(superposition,[],[f65,f111])).

fof(f111,plain,(
    ! [X4] : k3_xboole_0(k3_xboole_0(X4,X4),k3_xboole_0(X4,X4)) = X4 ),
    inference(forward_demodulation,[],[f102,f68])).

fof(f102,plain,(
    ! [X4] : k3_xboole_0(k3_xboole_0(X4,X4),k3_xboole_0(X4,X4)) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f96,f67])).

fof(f96,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X8),X9)) = X9 ),
    inference(forward_demodulation,[],[f85,f69])).

fof(f85,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X8),X9)) = k5_xboole_0(k1_xboole_0,X9) ),
    inference(superposition,[],[f43,f67])).

fof(f100,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X0))) = X1 ),
    inference(superposition,[],[f96,f32])).

fof(f730,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f63,f729])).

fof(f729,plain,(
    ! [X17,X16] : k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16) = k3_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X17)) ),
    inference(forward_demodulation,[],[f728,f69])).

fof(f728,plain,(
    ! [X17,X16] : k3_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X17)) = k5_xboole_0(k1_xboole_0,k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16)) ),
    inference(forward_demodulation,[],[f719,f32])).

fof(f719,plain,(
    ! [X17,X16] : k3_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X17)) = k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k1_xboole_0) ),
    inference(superposition,[],[f203,f115])).

fof(f115,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(resolution,[],[f57,f59])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f30,f54,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f44,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f45,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f46,f47])).

fof(f47,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f53])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f203,plain,(
    ! [X8,X9] : k5_xboole_0(X8,k5_xboole_0(X8,X9)) = X9 ),
    inference(backward_demodulation,[],[f96,f201])).

fof(f63,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(backward_demodulation,[],[f55,f31])).

fof(f55,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f27,f53,f48,f54,f53])).

fof(f27,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:20:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (12986)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.50  % (12994)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.51  % (12985)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (12984)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (12984)Refutation not found, incomplete strategy% (12984)------------------------------
% 0.21/0.52  % (12984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12984)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12984)Memory used [KB]: 6140
% 0.21/0.52  % (12984)Time elapsed: 0.099 s
% 0.21/0.52  % (12984)------------------------------
% 0.21/0.52  % (12984)------------------------------
% 0.21/0.52  % (12974)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (12974)Refutation not found, incomplete strategy% (12974)------------------------------
% 0.21/0.52  % (12974)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12974)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12974)Memory used [KB]: 1663
% 0.21/0.52  % (12974)Time elapsed: 0.106 s
% 0.21/0.52  % (12974)------------------------------
% 0.21/0.52  % (12974)------------------------------
% 0.21/0.52  % (12995)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (12973)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (12978)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (12975)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (13002)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (12979)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (13002)Refutation not found, incomplete strategy% (13002)------------------------------
% 0.21/0.53  % (13002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13002)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13002)Memory used [KB]: 1663
% 0.21/0.53  % (13002)Time elapsed: 0.118 s
% 0.21/0.53  % (13002)------------------------------
% 0.21/0.53  % (13002)------------------------------
% 1.34/0.53  % (12985)Refutation not found, incomplete strategy% (12985)------------------------------
% 1.34/0.53  % (12985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (12985)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (12985)Memory used [KB]: 10618
% 1.34/0.53  % (12985)Time elapsed: 0.115 s
% 1.34/0.53  % (12985)------------------------------
% 1.34/0.53  % (12985)------------------------------
% 1.34/0.53  % (12998)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.53  % (13000)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.53  % (12981)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.34/0.53  % (13000)Refutation not found, incomplete strategy% (13000)------------------------------
% 1.34/0.53  % (13000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (13000)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (13000)Memory used [KB]: 6140
% 1.34/0.53  % (13000)Time elapsed: 0.120 s
% 1.34/0.53  % (13000)------------------------------
% 1.34/0.53  % (13000)------------------------------
% 1.34/0.53  % (12987)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.53  % (12982)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.34/0.53  % (12987)Refutation not found, incomplete strategy% (12987)------------------------------
% 1.34/0.53  % (12987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (12987)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (12987)Memory used [KB]: 1663
% 1.34/0.53  % (12987)Time elapsed: 0.080 s
% 1.34/0.53  % (12987)------------------------------
% 1.34/0.53  % (12987)------------------------------
% 1.34/0.53  % (13001)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.54  % (13001)Refutation not found, incomplete strategy% (13001)------------------------------
% 1.34/0.54  % (13001)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (13001)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (13001)Memory used [KB]: 10618
% 1.34/0.54  % (13001)Time elapsed: 0.129 s
% 1.34/0.54  % (13001)------------------------------
% 1.34/0.54  % (13001)------------------------------
% 1.34/0.54  % (12997)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.34/0.54  % (12976)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.34/0.54  % (12993)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.34/0.54  % (12997)Refutation not found, incomplete strategy% (12997)------------------------------
% 1.34/0.54  % (12997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (12997)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (12997)Memory used [KB]: 10618
% 1.34/0.54  % (12997)Time elapsed: 0.129 s
% 1.34/0.54  % (12997)------------------------------
% 1.34/0.54  % (12997)------------------------------
% 1.34/0.54  % (12999)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.34/0.54  % (12990)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.34/0.54  % (12977)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.34/0.54  % (12990)Refutation not found, incomplete strategy% (12990)------------------------------
% 1.34/0.54  % (12990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (12990)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (12990)Memory used [KB]: 1663
% 1.34/0.54  % (12990)Time elapsed: 0.126 s
% 1.34/0.54  % (12990)------------------------------
% 1.34/0.54  % (12990)------------------------------
% 1.34/0.54  % (12998)Refutation not found, incomplete strategy% (12998)------------------------------
% 1.34/0.54  % (12998)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (12998)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (12998)Memory used [KB]: 6140
% 1.34/0.54  % (12998)Time elapsed: 0.127 s
% 1.34/0.54  % (12998)------------------------------
% 1.34/0.54  % (12998)------------------------------
% 1.34/0.55  % (12989)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.52/0.55  % (12989)Refutation not found, incomplete strategy% (12989)------------------------------
% 1.52/0.55  % (12989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.55  % (12989)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.55  
% 1.52/0.55  % (12989)Memory used [KB]: 10618
% 1.52/0.55  % (12989)Time elapsed: 0.135 s
% 1.52/0.55  % (12989)------------------------------
% 1.52/0.55  % (12989)------------------------------
% 1.52/0.55  % (12991)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.52/0.55  % (12983)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.52/0.55  % (12992)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.52/0.55  % (12988)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.52/0.55  % (12991)Refutation not found, incomplete strategy% (12991)------------------------------
% 1.52/0.55  % (12991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.55  % (12999)Refutation not found, incomplete strategy% (12999)------------------------------
% 1.52/0.55  % (12999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.55  % (12999)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.55  
% 1.52/0.55  % (12999)Memory used [KB]: 6140
% 1.52/0.55  % (12999)Time elapsed: 0.139 s
% 1.52/0.55  % (12999)------------------------------
% 1.52/0.55  % (12999)------------------------------
% 1.52/0.55  % (12996)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.52/0.55  % (12980)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.52/0.56  % (12991)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (12991)Memory used [KB]: 1663
% 1.52/0.56  % (12991)Time elapsed: 0.140 s
% 1.52/0.56  % (12991)------------------------------
% 1.52/0.56  % (12991)------------------------------
% 1.52/0.56  % (12983)Refutation not found, incomplete strategy% (12983)------------------------------
% 1.52/0.56  % (12983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.56  % (12983)Termination reason: Refutation not found, incomplete strategy
% 1.52/0.56  
% 1.52/0.56  % (12983)Memory used [KB]: 10618
% 1.52/0.56  % (12983)Time elapsed: 0.151 s
% 1.52/0.56  % (12983)------------------------------
% 1.52/0.56  % (12983)------------------------------
% 1.52/0.62  % (12995)Refutation found. Thanks to Tanya!
% 1.52/0.62  % SZS status Theorem for theBenchmark
% 1.89/0.63  % SZS output start Proof for theBenchmark
% 1.89/0.63  fof(f735,plain,(
% 1.89/0.63    $false),
% 1.89/0.63    inference(subsumption_resolution,[],[f730,f204])).
% 1.89/0.63  fof(f204,plain,(
% 1.89/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,X0)) = X1) )),
% 1.89/0.63    inference(backward_demodulation,[],[f100,f201])).
% 1.89/0.63  fof(f201,plain,(
% 1.89/0.63    ( ! [X4] : (k3_xboole_0(X4,X4) = X4) )),
% 1.89/0.63    inference(forward_demodulation,[],[f200,f68])).
% 1.89/0.63  fof(f68,plain,(
% 1.89/0.63    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.89/0.63    inference(backward_demodulation,[],[f56,f67])).
% 1.89/0.63  fof(f67,plain,(
% 1.89/0.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 1.89/0.63    inference(resolution,[],[f59,f61])).
% 1.89/0.63  fof(f61,plain,(
% 1.89/0.63    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.89/0.63    inference(equality_resolution,[],[f38])).
% 1.89/0.63  fof(f38,plain,(
% 1.89/0.63    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.89/0.63    inference(cnf_transformation,[],[f25])).
% 1.89/0.63  fof(f25,plain,(
% 1.89/0.63    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.63    inference(flattening,[],[f24])).
% 1.89/0.63  fof(f24,plain,(
% 1.89/0.63    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.89/0.63    inference(nnf_transformation,[],[f4])).
% 1.89/0.63  fof(f4,axiom,(
% 1.89/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.89/0.63  fof(f59,plain,(
% 1.89/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.89/0.63    inference(definition_unfolding,[],[f41,f34])).
% 1.89/0.63  fof(f34,plain,(
% 1.89/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.89/0.63    inference(cnf_transformation,[],[f6])).
% 1.89/0.63  fof(f6,axiom,(
% 1.89/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.89/0.63  fof(f41,plain,(
% 1.89/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.89/0.63    inference(cnf_transformation,[],[f26])).
% 1.89/0.63  fof(f26,plain,(
% 1.89/0.63    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.89/0.63    inference(nnf_transformation,[],[f5])).
% 1.89/0.63  fof(f5,axiom,(
% 1.89/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.89/0.63  fof(f56,plain,(
% 1.89/0.63    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 1.89/0.63    inference(definition_unfolding,[],[f29,f48])).
% 1.89/0.63  fof(f48,plain,(
% 1.89/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.89/0.63    inference(definition_unfolding,[],[f35,f34])).
% 1.89/0.63  fof(f35,plain,(
% 1.89/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.89/0.63    inference(cnf_transformation,[],[f9])).
% 1.89/0.63  fof(f9,axiom,(
% 1.89/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.89/0.63  fof(f29,plain,(
% 1.89/0.63    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.89/0.63    inference(cnf_transformation,[],[f20])).
% 1.89/0.63  fof(f20,plain,(
% 1.89/0.63    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.89/0.63    inference(rectify,[],[f3])).
% 1.89/0.63  fof(f3,axiom,(
% 1.89/0.63    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.89/0.63  fof(f200,plain,(
% 1.89/0.63    ( ! [X4] : (k3_xboole_0(X4,X4) = k5_xboole_0(X4,k1_xboole_0)) )),
% 1.89/0.63    inference(backward_demodulation,[],[f156,f190])).
% 1.89/0.63  fof(f190,plain,(
% 1.89/0.63    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 1.89/0.63    inference(superposition,[],[f174,f31])).
% 1.89/0.63  fof(f31,plain,(
% 1.89/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.89/0.63    inference(cnf_transformation,[],[f1])).
% 1.89/0.63  fof(f1,axiom,(
% 1.89/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.89/0.63  fof(f174,plain,(
% 1.89/0.63    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 1.89/0.63    inference(superposition,[],[f161,f68])).
% 1.89/0.63  fof(f161,plain,(
% 1.89/0.63    ( ! [X8] : (k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_xboole_0,X8),k1_xboole_0)) )),
% 1.89/0.63    inference(forward_demodulation,[],[f160,f67])).
% 1.89/0.63  fof(f160,plain,(
% 1.89/0.63    ( ! [X8] : (k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_xboole_0,X8),k5_xboole_0(k3_xboole_0(k1_xboole_0,X8),k3_xboole_0(k3_xboole_0(k1_xboole_0,X8),k3_xboole_0(k1_xboole_0,X8))))) )),
% 1.89/0.63    inference(forward_demodulation,[],[f144,f69])).
% 1.89/0.63  fof(f69,plain,(
% 1.89/0.63    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.89/0.63    inference(superposition,[],[f68,f32])).
% 1.89/0.63  fof(f32,plain,(
% 1.89/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.89/0.63    inference(cnf_transformation,[],[f2])).
% 1.89/0.63  fof(f2,axiom,(
% 1.89/0.63    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.89/0.63  fof(f144,plain,(
% 1.89/0.63    ( ! [X8] : (k1_xboole_0 = k5_xboole_0(k3_xboole_0(k1_xboole_0,X8),k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(k1_xboole_0,X8),k3_xboole_0(k3_xboole_0(k1_xboole_0,X8),k3_xboole_0(k1_xboole_0,X8)))))) )),
% 1.89/0.63    inference(superposition,[],[f65,f69])).
% 1.89/0.63  fof(f65,plain,(
% 1.89/0.63    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))))) = X0) )),
% 1.89/0.63    inference(backward_demodulation,[],[f64,f43])).
% 1.89/0.63  fof(f43,plain,(
% 1.89/0.63    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.89/0.63    inference(cnf_transformation,[],[f8])).
% 1.89/0.63  fof(f8,axiom,(
% 1.89/0.63    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.89/0.63  fof(f64,plain,(
% 1.89/0.63    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))))) = X0) )),
% 1.89/0.63    inference(forward_demodulation,[],[f58,f31])).
% 1.89/0.63  fof(f58,plain,(
% 1.89/0.63    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),k3_xboole_0(X0,X1)))) = X0) )),
% 1.89/0.63    inference(definition_unfolding,[],[f36,f48,f34])).
% 1.89/0.63  fof(f36,plain,(
% 1.89/0.63    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.89/0.63    inference(cnf_transformation,[],[f7])).
% 1.89/0.63  fof(f7,axiom,(
% 1.89/0.63    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.89/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.89/0.63  fof(f156,plain,(
% 1.89/0.63    ( ! [X4] : (k3_xboole_0(X4,X4) = k5_xboole_0(X4,k3_xboole_0(X4,k1_xboole_0))) )),
% 1.89/0.63    inference(forward_demodulation,[],[f155,f67])).
% 1.89/0.63  fof(f155,plain,(
% 1.89/0.63    ( ! [X4] : (k3_xboole_0(X4,X4) = k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(X4,k3_xboole_0(X4,X4))))) )),
% 1.89/0.63    inference(forward_demodulation,[],[f154,f32])).
% 1.89/0.63  fof(f154,plain,(
% 1.89/0.63    ( ! [X4] : (k3_xboole_0(X4,X4) = k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X4),X4)))) )),
% 1.89/0.63    inference(forward_demodulation,[],[f153,f100])).
% 1.89/0.63  fof(f153,plain,(
% 1.89/0.63    ( ! [X4] : (k3_xboole_0(X4,X4) = k5_xboole_0(X4,k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X4),X4)),k3_xboole_0(X4,X4))))) )),
% 1.89/0.63    inference(forward_demodulation,[],[f141,f88])).
% 1.89/0.63  fof(f88,plain,(
% 1.89/0.63    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) )),
% 1.89/0.63    inference(superposition,[],[f43,f32])).
% 1.89/0.63  fof(f141,plain,(
% 1.89/0.63    ( ! [X4] : (k3_xboole_0(X4,X4) = k5_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X4),k5_xboole_0(X4,k3_xboole_0(X4,k5_xboole_0(k3_xboole_0(X4,X4),X4)))))) )),
% 1.89/0.63    inference(superposition,[],[f65,f111])).
% 1.89/0.63  fof(f111,plain,(
% 1.89/0.63    ( ! [X4] : (k3_xboole_0(k3_xboole_0(X4,X4),k3_xboole_0(X4,X4)) = X4) )),
% 1.89/0.63    inference(forward_demodulation,[],[f102,f68])).
% 1.89/0.63  fof(f102,plain,(
% 1.89/0.63    ( ! [X4] : (k3_xboole_0(k3_xboole_0(X4,X4),k3_xboole_0(X4,X4)) = k5_xboole_0(X4,k1_xboole_0)) )),
% 1.89/0.63    inference(superposition,[],[f96,f67])).
% 1.89/0.63  fof(f96,plain,(
% 1.89/0.63    ( ! [X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X8),X9)) = X9) )),
% 1.89/0.63    inference(forward_demodulation,[],[f85,f69])).
% 1.89/0.63  fof(f85,plain,(
% 1.89/0.63    ( ! [X8,X9] : (k5_xboole_0(X8,k5_xboole_0(k3_xboole_0(X8,X8),X9)) = k5_xboole_0(k1_xboole_0,X9)) )),
% 1.89/0.63    inference(superposition,[],[f43,f67])).
% 1.89/0.64  fof(f100,plain,(
% 1.89/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X0))) = X1) )),
% 1.89/0.64    inference(superposition,[],[f96,f32])).
% 1.89/0.64  fof(f730,plain,(
% 1.89/0.64    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.89/0.64    inference(backward_demodulation,[],[f63,f729])).
% 1.89/0.64  fof(f729,plain,(
% 1.89/0.64    ( ! [X17,X16] : (k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16) = k3_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X17))) )),
% 1.89/0.64    inference(forward_demodulation,[],[f728,f69])).
% 1.89/0.64  fof(f728,plain,(
% 1.89/0.64    ( ! [X17,X16] : (k3_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X17)) = k5_xboole_0(k1_xboole_0,k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16))) )),
% 1.89/0.64    inference(forward_demodulation,[],[f719,f32])).
% 1.89/0.64  fof(f719,plain,(
% 1.89/0.64    ( ! [X17,X16] : (k3_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X17)) = k5_xboole_0(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X16),k1_xboole_0)) )),
% 1.89/0.64    inference(superposition,[],[f203,f115])).
% 1.89/0.64  fof(f115,plain,(
% 1.89/0.64    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.89/0.64    inference(resolution,[],[f57,f59])).
% 1.89/0.64  fof(f57,plain,(
% 1.89/0.64    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.89/0.64    inference(definition_unfolding,[],[f30,f54,f53])).
% 1.89/0.64  fof(f53,plain,(
% 1.89/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.89/0.64    inference(definition_unfolding,[],[f33,f52])).
% 1.89/0.64  fof(f52,plain,(
% 1.89/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.89/0.64    inference(definition_unfolding,[],[f42,f51])).
% 1.89/0.64  fof(f51,plain,(
% 1.89/0.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.89/0.64    inference(definition_unfolding,[],[f44,f50])).
% 1.89/0.64  fof(f50,plain,(
% 1.89/0.64    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.89/0.64    inference(definition_unfolding,[],[f45,f49])).
% 1.89/0.64  fof(f49,plain,(
% 1.89/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.89/0.64    inference(definition_unfolding,[],[f46,f47])).
% 1.89/0.64  fof(f47,plain,(
% 1.89/0.64    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f16])).
% 1.89/0.64  fof(f16,axiom,(
% 1.89/0.64    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.89/0.64  fof(f46,plain,(
% 1.89/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f15])).
% 1.89/0.64  fof(f15,axiom,(
% 1.89/0.64    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.89/0.64  fof(f45,plain,(
% 1.89/0.64    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f14])).
% 1.89/0.64  fof(f14,axiom,(
% 1.89/0.64    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.89/0.64  fof(f44,plain,(
% 1.89/0.64    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f13])).
% 1.89/0.64  fof(f13,axiom,(
% 1.89/0.64    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.89/0.64  fof(f42,plain,(
% 1.89/0.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f12])).
% 1.89/0.64  fof(f12,axiom,(
% 1.89/0.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.89/0.64  fof(f33,plain,(
% 1.89/0.64    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f11])).
% 1.89/0.64  fof(f11,axiom,(
% 1.89/0.64    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.89/0.64  fof(f54,plain,(
% 1.89/0.64    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.89/0.64    inference(definition_unfolding,[],[f28,f53])).
% 1.89/0.64  fof(f28,plain,(
% 1.89/0.64    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.89/0.64    inference(cnf_transformation,[],[f10])).
% 1.89/0.64  fof(f10,axiom,(
% 1.89/0.64    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.89/0.64  fof(f30,plain,(
% 1.89/0.64    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.89/0.64    inference(cnf_transformation,[],[f17])).
% 1.89/0.64  fof(f17,axiom,(
% 1.89/0.64    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.89/0.64  fof(f203,plain,(
% 1.89/0.64    ( ! [X8,X9] : (k5_xboole_0(X8,k5_xboole_0(X8,X9)) = X9) )),
% 1.89/0.64    inference(backward_demodulation,[],[f96,f201])).
% 1.89/0.64  fof(f63,plain,(
% 1.89/0.64    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.89/0.64    inference(backward_demodulation,[],[f55,f31])).
% 1.89/0.64  fof(f55,plain,(
% 1.89/0.64    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 1.89/0.64    inference(definition_unfolding,[],[f27,f53,f48,f54,f53])).
% 1.89/0.64  fof(f27,plain,(
% 1.89/0.64    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.89/0.64    inference(cnf_transformation,[],[f23])).
% 1.89/0.64  fof(f23,plain,(
% 1.89/0.64    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.89/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f22])).
% 1.89/0.64  fof(f22,plain,(
% 1.89/0.64    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 1.89/0.64    introduced(choice_axiom,[])).
% 1.89/0.64  fof(f21,plain,(
% 1.89/0.64    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.89/0.64    inference(ennf_transformation,[],[f19])).
% 1.89/0.64  fof(f19,negated_conjecture,(
% 1.89/0.64    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.89/0.64    inference(negated_conjecture,[],[f18])).
% 1.89/0.64  fof(f18,conjecture,(
% 1.89/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.89/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 1.89/0.64  % SZS output end Proof for theBenchmark
% 1.89/0.64  % (12995)------------------------------
% 1.89/0.64  % (12995)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.64  % (12995)Termination reason: Refutation
% 1.89/0.64  
% 1.89/0.64  % (12995)Memory used [KB]: 7291
% 1.89/0.64  % (12995)Time elapsed: 0.175 s
% 1.89/0.64  % (12995)------------------------------
% 1.89/0.64  % (12995)------------------------------
% 1.89/0.64  % (12972)Success in time 0.272 s
%------------------------------------------------------------------------------

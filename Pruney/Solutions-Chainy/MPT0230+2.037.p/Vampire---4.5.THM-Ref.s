%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:36:39 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 325 expanded)
%              Number of leaves         :   21 ( 106 expanded)
%              Depth                    :   17
%              Number of atoms          :  133 ( 408 expanded)
%              Number of equality atoms :   92 ( 346 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f958,plain,(
    $false ),
    inference(resolution,[],[f928,f189])).

fof(f189,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(unit_resulting_resolution,[],[f81,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | ~ sP4(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f44,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f81,plain,(
    ! [X4,X2,X1] : sP4(X4,X2,X1,X4) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X1] :
      ( X0 != X4
      | sP4(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f928,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f184,f926])).

fof(f926,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f925,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f43,f61,f61])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(f925,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f924,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f42,f61,f61])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(f924,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
    inference(forward_demodulation,[],[f908,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f908,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f76,f347])).

fof(f347,plain,(
    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f65,f310])).

fof(f310,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(backward_demodulation,[],[f117,f302])).

fof(f302,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f134,f301])).

fof(f301,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f294,f31])).

fof(f294,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0) ),
    inference(superposition,[],[f64,f134])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f39,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f134,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f118,f68])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f36,f40,f40])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f118,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f116,f31])).

fof(f116,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f64,f82])).

fof(f82,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f67,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f35,f40])).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f117,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X1,X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f115,f114])).

fof(f114,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f64,f66])).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f34,f40])).

fof(f34,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f115,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f64,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f65,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f28,f63,f62])).

fof(f62,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f61])).

fof(f37,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f63,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f62])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f76,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5))) ),
    inference(definition_unfolding,[],[f57,f56,f38,f58,f63])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(f184,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(forward_demodulation,[],[f183,f70])).

fof(f183,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f158,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | sP4(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP4(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f51,f61])).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP4(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f158,plain,(
    ~ sP4(sK0,sK1,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f30,f29,f29,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f29,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f30,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:25:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (13705)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (13697)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (13706)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (13687)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (13686)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (13689)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (13685)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (13698)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (13712)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.52  % (13688)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.53  % (13683)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.53  % (13693)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.53  % (13683)Refutation not found, incomplete strategy% (13683)------------------------------
% 1.29/0.53  % (13683)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (13683)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (13683)Memory used [KB]: 1663
% 1.29/0.53  % (13683)Time elapsed: 0.090 s
% 1.29/0.53  % (13683)------------------------------
% 1.29/0.53  % (13683)------------------------------
% 1.29/0.53  % (13698)Refutation not found, incomplete strategy% (13698)------------------------------
% 1.29/0.53  % (13698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (13704)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.53  % (13706)Refutation not found, incomplete strategy% (13706)------------------------------
% 1.29/0.53  % (13706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (13693)Refutation not found, incomplete strategy% (13693)------------------------------
% 1.29/0.53  % (13693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.53  % (13693)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (13693)Memory used [KB]: 10618
% 1.29/0.53  % (13693)Time elapsed: 0.123 s
% 1.29/0.53  % (13693)------------------------------
% 1.29/0.53  % (13693)------------------------------
% 1.29/0.53  % (13708)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.53  % (13706)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (13706)Memory used [KB]: 1791
% 1.29/0.53  % (13706)Time elapsed: 0.115 s
% 1.29/0.53  % (13706)------------------------------
% 1.29/0.53  % (13706)------------------------------
% 1.29/0.53  % (13698)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.53  
% 1.29/0.53  % (13698)Memory used [KB]: 6268
% 1.29/0.53  % (13698)Time elapsed: 0.121 s
% 1.29/0.53  % (13698)------------------------------
% 1.29/0.53  % (13698)------------------------------
% 1.29/0.53  % (13702)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.53  % (13696)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.54  % (13690)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.54  % (13695)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.54  % (13684)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.54  % (13707)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.54  % (13710)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.54  % (13700)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.54  % (13699)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.54  % (13700)Refutation not found, incomplete strategy% (13700)------------------------------
% 1.29/0.54  % (13700)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.54  % (13700)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.54  
% 1.29/0.54  % (13700)Memory used [KB]: 10618
% 1.29/0.54  % (13700)Time elapsed: 0.127 s
% 1.29/0.54  % (13700)------------------------------
% 1.29/0.54  % (13700)------------------------------
% 1.41/0.55  % (13711)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.41/0.55  % (13701)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.55  % (13691)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.41/0.55  % (13692)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.55  % (13703)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.55  % (13692)Refutation not found, incomplete strategy% (13692)------------------------------
% 1.41/0.55  % (13692)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (13692)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (13692)Memory used [KB]: 10618
% 1.41/0.55  % (13692)Time elapsed: 0.138 s
% 1.41/0.55  % (13692)------------------------------
% 1.41/0.55  % (13692)------------------------------
% 1.41/0.55  % (13703)Refutation not found, incomplete strategy% (13703)------------------------------
% 1.41/0.55  % (13703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (13703)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (13703)Memory used [KB]: 10746
% 1.41/0.55  % (13703)Time elapsed: 0.141 s
% 1.41/0.55  % (13703)------------------------------
% 1.41/0.55  % (13703)------------------------------
% 1.41/0.56  % (13694)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.41/0.56  % (13694)Refutation not found, incomplete strategy% (13694)------------------------------
% 1.41/0.56  % (13694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (13694)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (13694)Memory used [KB]: 10618
% 1.41/0.56  % (13694)Time elapsed: 0.150 s
% 1.41/0.56  % (13694)------------------------------
% 1.41/0.56  % (13694)------------------------------
% 1.41/0.56  % (13709)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.41/0.60  % (13707)Refutation found. Thanks to Tanya!
% 1.41/0.60  % SZS status Theorem for theBenchmark
% 1.41/0.60  % SZS output start Proof for theBenchmark
% 1.41/0.60  fof(f958,plain,(
% 1.41/0.60    $false),
% 1.41/0.60    inference(resolution,[],[f928,f189])).
% 1.41/0.60  fof(f189,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 1.41/0.60    inference(unit_resulting_resolution,[],[f81,f78])).
% 1.41/0.60  fof(f78,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | ~sP4(X4,X2,X1,X0)) )),
% 1.41/0.60    inference(equality_resolution,[],[f75])).
% 1.41/0.60  fof(f75,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X3,X1] : (~sP4(X4,X2,X1,X0) | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.41/0.60    inference(definition_unfolding,[],[f50,f61])).
% 1.41/0.60  fof(f61,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f44,f60])).
% 1.41/0.60  fof(f60,plain,(
% 1.41/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f45,f59])).
% 1.41/0.60  fof(f59,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f54,f58])).
% 1.41/0.60  fof(f58,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f55,f56])).
% 1.41/0.60  fof(f56,plain,(
% 1.41/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f19])).
% 1.41/0.60  fof(f19,axiom,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.41/0.60  fof(f55,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f18])).
% 1.41/0.60  fof(f18,axiom,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.41/0.60  fof(f54,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f17])).
% 1.41/0.60  fof(f17,axiom,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.41/0.60  fof(f45,plain,(
% 1.41/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f16])).
% 1.41/0.60  fof(f16,axiom,(
% 1.41/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.41/0.60  fof(f44,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f15])).
% 1.41/0.60  fof(f15,axiom,(
% 1.41/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.41/0.60  fof(f50,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X3,X1] : (~sP4(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.41/0.60    inference(cnf_transformation,[],[f27])).
% 1.41/0.60  fof(f27,plain,(
% 1.41/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.41/0.60    inference(ennf_transformation,[],[f10])).
% 1.41/0.60  fof(f10,axiom,(
% 1.41/0.60    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.41/0.60  fof(f81,plain,(
% 1.41/0.60    ( ! [X4,X2,X1] : (sP4(X4,X2,X1,X4)) )),
% 1.41/0.60    inference(equality_resolution,[],[f46])).
% 1.41/0.60  fof(f46,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X1] : (X0 != X4 | sP4(X4,X2,X1,X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f27])).
% 1.41/0.60  fof(f928,plain,(
% 1.41/0.60    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2))),
% 1.41/0.60    inference(backward_demodulation,[],[f184,f926])).
% 1.41/0.60  fof(f926,plain,(
% 1.41/0.60    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 1.41/0.60    inference(forward_demodulation,[],[f925,f71])).
% 1.41/0.60  fof(f71,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f43,f61,f61])).
% 1.41/0.60  fof(f43,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f20])).
% 1.41/0.60  fof(f20,axiom,(
% 1.41/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).
% 1.41/0.60  fof(f925,plain,(
% 1.41/0.60    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2,sK1)),
% 1.41/0.60    inference(forward_demodulation,[],[f924,f70])).
% 1.41/0.60  fof(f70,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f42,f61,f61])).
% 1.41/0.60  fof(f42,plain,(
% 1.41/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f11])).
% 1.41/0.60  fof(f11,axiom,(
% 1.41/0.60    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).
% 1.41/0.60  fof(f924,plain,(
% 1.41/0.60    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK0)),
% 1.41/0.60    inference(forward_demodulation,[],[f908,f31])).
% 1.41/0.60  fof(f31,plain,(
% 1.41/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.41/0.60    inference(cnf_transformation,[],[f8])).
% 1.41/0.60  fof(f8,axiom,(
% 1.41/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.41/0.60  fof(f908,plain,(
% 1.41/0.60    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK0) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0)),
% 1.41/0.60    inference(superposition,[],[f76,f347])).
% 1.41/0.60  fof(f347,plain,(
% 1.41/0.60    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.41/0.60    inference(unit_resulting_resolution,[],[f65,f310])).
% 1.41/0.60  fof(f310,plain,(
% 1.41/0.60    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 1.41/0.60    inference(backward_demodulation,[],[f117,f302])).
% 1.41/0.60  fof(f302,plain,(
% 1.41/0.60    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.41/0.60    inference(backward_demodulation,[],[f134,f301])).
% 1.41/0.60  fof(f301,plain,(
% 1.41/0.60    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = X3) )),
% 1.41/0.60    inference(forward_demodulation,[],[f294,f31])).
% 1.41/0.60  fof(f294,plain,(
% 1.41/0.60    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X3,k1_xboole_0)) )),
% 1.41/0.60    inference(superposition,[],[f64,f134])).
% 1.41/0.60  fof(f64,plain,(
% 1.41/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.41/0.60    inference(definition_unfolding,[],[f39,f40])).
% 1.41/0.60  fof(f40,plain,(
% 1.41/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.41/0.60    inference(cnf_transformation,[],[f7])).
% 1.41/0.60  fof(f7,axiom,(
% 1.41/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.41/0.60  fof(f39,plain,(
% 1.41/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.41/0.60    inference(cnf_transformation,[],[f3])).
% 1.41/0.60  fof(f3,axiom,(
% 1.41/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.41/0.60  fof(f134,plain,(
% 1.41/0.60    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 1.41/0.60    inference(superposition,[],[f118,f68])).
% 1.41/0.60  fof(f68,plain,(
% 1.41/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.41/0.60    inference(definition_unfolding,[],[f36,f40,f40])).
% 1.41/0.60  fof(f36,plain,(
% 1.41/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f1])).
% 1.41/0.60  fof(f1,axiom,(
% 1.41/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.41/0.60  fof(f118,plain,(
% 1.41/0.60    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 1.41/0.60    inference(forward_demodulation,[],[f116,f31])).
% 1.41/0.60  fof(f116,plain,(
% 1.41/0.60    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.41/0.60    inference(superposition,[],[f64,f82])).
% 1.41/0.60  fof(f82,plain,(
% 1.41/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.41/0.60    inference(unit_resulting_resolution,[],[f67,f33])).
% 1.41/0.60  fof(f33,plain,(
% 1.41/0.60    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.41/0.60    inference(cnf_transformation,[],[f25])).
% 1.41/0.60  fof(f25,plain,(
% 1.41/0.60    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.41/0.60    inference(ennf_transformation,[],[f6])).
% 1.41/0.60  fof(f6,axiom,(
% 1.41/0.60    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.41/0.60  fof(f67,plain,(
% 1.41/0.60    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f35,f40])).
% 1.41/0.60  fof(f35,plain,(
% 1.41/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f4])).
% 1.41/0.60  fof(f4,axiom,(
% 1.41/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.41/0.60  fof(f117,plain,(
% 1.41/0.60    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,X1) | ~r1_tarski(X1,X2)) )),
% 1.41/0.60    inference(forward_demodulation,[],[f115,f114])).
% 1.41/0.60  fof(f114,plain,(
% 1.41/0.60    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.41/0.60    inference(superposition,[],[f64,f66])).
% 1.41/0.60  fof(f66,plain,(
% 1.41/0.60    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.41/0.60    inference(definition_unfolding,[],[f34,f40])).
% 1.41/0.60  fof(f34,plain,(
% 1.41/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.41/0.60    inference(cnf_transformation,[],[f23])).
% 1.41/0.60  fof(f23,plain,(
% 1.41/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.41/0.60    inference(rectify,[],[f2])).
% 1.41/0.60  fof(f2,axiom,(
% 1.41/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.41/0.60  fof(f115,plain,(
% 1.41/0.60    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1) | ~r1_tarski(X1,X2)) )),
% 1.41/0.60    inference(superposition,[],[f64,f69])).
% 1.41/0.60  fof(f69,plain,(
% 1.41/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f41,f40])).
% 1.41/0.60  fof(f41,plain,(
% 1.41/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.41/0.60    inference(cnf_transformation,[],[f26])).
% 1.41/0.60  fof(f26,plain,(
% 1.41/0.60    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.41/0.60    inference(ennf_transformation,[],[f5])).
% 1.41/0.60  fof(f5,axiom,(
% 1.41/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.41/0.60  fof(f65,plain,(
% 1.41/0.60    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.41/0.60    inference(definition_unfolding,[],[f28,f63,f62])).
% 1.41/0.60  fof(f62,plain,(
% 1.41/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f37,f61])).
% 1.41/0.60  fof(f37,plain,(
% 1.41/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f14])).
% 1.41/0.60  fof(f14,axiom,(
% 1.41/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.41/0.60  fof(f63,plain,(
% 1.41/0.60    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.41/0.60    inference(definition_unfolding,[],[f32,f62])).
% 1.41/0.60  fof(f32,plain,(
% 1.41/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.41/0.60    inference(cnf_transformation,[],[f13])).
% 1.41/0.60  fof(f13,axiom,(
% 1.41/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.41/0.60  fof(f28,plain,(
% 1.41/0.60    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.41/0.60    inference(cnf_transformation,[],[f24])).
% 1.41/0.60  fof(f24,plain,(
% 1.41/0.60    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.41/0.60    inference(ennf_transformation,[],[f22])).
% 1.41/0.60  fof(f22,negated_conjecture,(
% 1.41/0.60    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.41/0.60    inference(negated_conjecture,[],[f21])).
% 1.41/0.60  fof(f21,conjecture,(
% 1.41/0.60    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.41/0.60  fof(f76,plain,(
% 1.41/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_xboole_0(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k4_xboole_0(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)))) )),
% 1.41/0.60    inference(definition_unfolding,[],[f57,f56,f38,f58,f63])).
% 1.41/0.60  fof(f38,plain,(
% 1.41/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.41/0.60    inference(cnf_transformation,[],[f9])).
% 1.41/0.60  fof(f9,axiom,(
% 1.41/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.41/0.60  fof(f57,plain,(
% 1.41/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 1.41/0.60    inference(cnf_transformation,[],[f12])).
% 1.41/0.60  fof(f12,axiom,(
% 1.41/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 1.41/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
% 1.41/0.60  fof(f184,plain,(
% 1.41/0.60    ~r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.41/0.60    inference(forward_demodulation,[],[f183,f70])).
% 1.41/0.60  fof(f183,plain,(
% 1.41/0.60    ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1,sK1))),
% 1.41/0.60    inference(unit_resulting_resolution,[],[f158,f77])).
% 1.41/0.60  fof(f77,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | sP4(X4,X2,X1,X0)) )),
% 1.41/0.60    inference(equality_resolution,[],[f74])).
% 1.41/0.60  fof(f74,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X3,X1] : (sP4(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.41/0.60    inference(definition_unfolding,[],[f51,f61])).
% 1.41/0.60  fof(f51,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X3,X1] : (sP4(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.41/0.60    inference(cnf_transformation,[],[f27])).
% 1.41/0.60  fof(f158,plain,(
% 1.41/0.60    ~sP4(sK0,sK1,sK1,sK2)),
% 1.41/0.60    inference(unit_resulting_resolution,[],[f30,f29,f29,f49])).
% 1.41/0.60  fof(f49,plain,(
% 1.41/0.60    ( ! [X4,X2,X0,X1] : (~sP4(X4,X2,X1,X0) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.41/0.60    inference(cnf_transformation,[],[f27])).
% 1.41/0.60  fof(f29,plain,(
% 1.41/0.60    sK0 != sK1),
% 1.41/0.60    inference(cnf_transformation,[],[f24])).
% 1.41/0.60  fof(f30,plain,(
% 1.41/0.60    sK0 != sK2),
% 1.41/0.60    inference(cnf_transformation,[],[f24])).
% 1.41/0.60  % SZS output end Proof for theBenchmark
% 1.41/0.60  % (13707)------------------------------
% 1.41/0.60  % (13707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.60  % (13707)Termination reason: Refutation
% 1.41/0.60  
% 1.41/0.60  % (13707)Memory used [KB]: 6780
% 1.41/0.60  % (13707)Time elapsed: 0.169 s
% 1.41/0.60  % (13707)------------------------------
% 1.41/0.60  % (13707)------------------------------
% 1.41/0.62  % (13681)Success in time 0.254 s
%------------------------------------------------------------------------------

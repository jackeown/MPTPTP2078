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
% DateTime   : Thu Dec  3 12:36:39 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   95 ( 447 expanded)
%              Number of leaves         :   20 ( 146 expanded)
%              Depth                    :   20
%              Number of atoms          :  130 ( 548 expanded)
%              Number of equality atoms :   93 ( 462 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f591,plain,(
    $false ),
    inference(resolution,[],[f570,f191])).

fof(f191,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(unit_resulting_resolution,[],[f80,f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | ~ sP4(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f49,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f53,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f54,f55])).

fof(f55,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f80,plain,(
    ! [X4,X2,X1] : sP4(X4,X2,X1,X4) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X1] :
      ( X0 != X4
      | sP4(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f570,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)) ),
    inference(backward_demodulation,[],[f186,f563])).

fof(f563,plain,(
    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(superposition,[],[f548,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f548,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f547,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1) ),
    inference(definition_unfolding,[],[f40,f60,f60])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

fof(f547,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(forward_demodulation,[],[f546,f213])).

fof(f213,plain,(
    ! [X6,X8,X7] : k6_enumset1(X6,X6,X6,X6,X6,X6,X8,X7) = k6_enumset1(X8,X8,X8,X8,X8,X8,X7,X6) ),
    inference(superposition,[],[f70,f69])).

fof(f70,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f41,f60,f60])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).

fof(f546,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0,sK2) ),
    inference(forward_demodulation,[],[f535,f69])).

fof(f535,plain,(
    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK0) ),
    inference(superposition,[],[f71,f279])).

fof(f279,plain,(
    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f65,f151])).

fof(f151,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(backward_demodulation,[],[f102,f145])).

fof(f145,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(X7,X7) ),
    inference(backward_demodulation,[],[f131,f144])).

fof(f144,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = X2 ),
    inference(forward_demodulation,[],[f140,f31])).

fof(f140,plain,(
    ! [X2] : k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0) ),
    inference(superposition,[],[f63,f131])).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f131,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(X7,k4_xboole_0(X7,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f115,f85])).

fof(f85,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f81,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f30,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f115,plain,(
    ! [X7] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X7,k4_xboole_0(X7,k1_xboole_0)) ),
    inference(superposition,[],[f67,f103])).

fof(f103,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f101,f31])).

fof(f101,plain,(
    ! [X3] : k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f63,f81])).

fof(f67,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f34,f38,f38])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f102,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = k4_xboole_0(X1,X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(forward_demodulation,[],[f100,f99])).

fof(f99,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f63,f66])).

fof(f66,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f100,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f63,f68])).

fof(f65,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f27,f62,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f60])).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f61])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) ),
    inference(definition_unfolding,[],[f44,f59,f36,f60,f62])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f186,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(forward_demodulation,[],[f185,f70])).

fof(f185,plain,(
    ~ r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f160,f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | sP4(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP4(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f60])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP4(X4,X2,X1,X0)
      | ~ r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f160,plain,(
    ~ sP4(sK0,sK1,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f29,f28,f28,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X4,X2,X1,X0)
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f28,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f29,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : run_vampire %s %d
% 0.11/0.33  % Computer   : n020.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 18:36:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.20/0.50  % (27080)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.50  % (27097)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.50  % (27083)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.50  % (27086)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.50  % (27080)Refutation not found, incomplete strategy% (27080)------------------------------
% 0.20/0.50  % (27080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27080)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (27080)Memory used [KB]: 1663
% 0.20/0.50  % (27080)Time elapsed: 0.092 s
% 0.20/0.50  % (27080)------------------------------
% 0.20/0.50  % (27080)------------------------------
% 0.20/0.50  % (27084)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (27090)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.50  % (27103)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (27084)Refutation not found, incomplete strategy% (27084)------------------------------
% 0.20/0.50  % (27084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (27084)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (27084)Memory used [KB]: 6140
% 0.20/0.50  % (27084)Time elapsed: 0.095 s
% 0.20/0.50  % (27084)------------------------------
% 0.20/0.50  % (27084)------------------------------
% 0.20/0.51  % (27090)Refutation not found, incomplete strategy% (27090)------------------------------
% 0.20/0.51  % (27090)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27090)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (27090)Memory used [KB]: 10618
% 0.20/0.51  % (27090)Time elapsed: 0.096 s
% 0.20/0.51  % (27090)------------------------------
% 0.20/0.51  % (27090)------------------------------
% 0.20/0.51  % (27097)Refutation not found, incomplete strategy% (27097)------------------------------
% 0.20/0.51  % (27097)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27089)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (27097)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (27097)Memory used [KB]: 10618
% 0.20/0.51  % (27097)Time elapsed: 0.099 s
% 0.20/0.51  % (27097)------------------------------
% 0.20/0.51  % (27097)------------------------------
% 0.20/0.51  % (27103)Refutation not found, incomplete strategy% (27103)------------------------------
% 0.20/0.51  % (27103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27103)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (27103)Memory used [KB]: 1791
% 0.20/0.51  % (27103)Time elapsed: 0.062 s
% 0.20/0.51  % (27103)------------------------------
% 0.20/0.51  % (27103)------------------------------
% 0.20/0.51  % (27082)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (27081)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (27089)Refutation not found, incomplete strategy% (27089)------------------------------
% 0.20/0.51  % (27089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27089)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (27089)Memory used [KB]: 10618
% 0.20/0.51  % (27089)Time elapsed: 0.108 s
% 0.20/0.51  % (27089)------------------------------
% 0.20/0.51  % (27089)------------------------------
% 0.20/0.51  % (27082)Refutation not found, incomplete strategy% (27082)------------------------------
% 0.20/0.51  % (27082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27082)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (27082)Memory used [KB]: 10746
% 0.20/0.51  % (27082)Time elapsed: 0.106 s
% 0.20/0.51  % (27082)------------------------------
% 0.20/0.51  % (27082)------------------------------
% 0.20/0.51  % (27088)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (27100)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.51  % (27108)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.51  % (27100)Refutation not found, incomplete strategy% (27100)------------------------------
% 0.20/0.51  % (27100)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (27100)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (27100)Memory used [KB]: 10746
% 0.20/0.51  % (27100)Time elapsed: 0.112 s
% 0.20/0.51  % (27100)------------------------------
% 0.20/0.51  % (27100)------------------------------
% 0.20/0.52  % (27099)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.52  % (27102)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (27091)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (27106)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.52  % (27094)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (27107)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.52  % (27091)Refutation not found, incomplete strategy% (27091)------------------------------
% 0.20/0.52  % (27091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27091)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27091)Memory used [KB]: 10618
% 0.20/0.53  % (27091)Time elapsed: 0.127 s
% 0.20/0.53  % (27091)------------------------------
% 0.20/0.53  % (27091)------------------------------
% 0.20/0.53  % (27093)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.53  % (27095)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (27109)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (27085)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (27095)Refutation not found, incomplete strategy% (27095)------------------------------
% 0.20/0.53  % (27095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27095)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27095)Memory used [KB]: 6268
% 0.20/0.53  % (27095)Time elapsed: 0.092 s
% 0.20/0.53  % (27095)------------------------------
% 0.20/0.53  % (27095)------------------------------
% 0.20/0.53  % (27092)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (27101)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.53  % (27105)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (27101)Refutation not found, incomplete strategy% (27101)------------------------------
% 0.20/0.53  % (27101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27101)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27101)Memory used [KB]: 1791
% 0.20/0.53  % (27101)Time elapsed: 0.129 s
% 0.20/0.53  % (27101)------------------------------
% 0.20/0.53  % (27101)------------------------------
% 0.20/0.53  % (27088)Refutation not found, incomplete strategy% (27088)------------------------------
% 0.20/0.53  % (27088)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27088)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27088)Memory used [KB]: 10746
% 0.20/0.53  % (27088)Time elapsed: 0.125 s
% 0.20/0.53  % (27088)------------------------------
% 0.20/0.53  % (27088)------------------------------
% 0.20/0.53  % (27105)Refutation not found, incomplete strategy% (27105)------------------------------
% 0.20/0.53  % (27105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (27105)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (27105)Memory used [KB]: 6396
% 0.20/0.53  % (27105)Time elapsed: 0.106 s
% 0.20/0.53  % (27105)------------------------------
% 0.20/0.53  % (27105)------------------------------
% 1.45/0.54  % (27106)Refutation not found, incomplete strategy% (27106)------------------------------
% 1.45/0.54  % (27106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (27106)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.54  
% 1.45/0.54  % (27106)Memory used [KB]: 10874
% 1.45/0.54  % (27106)Time elapsed: 0.130 s
% 1.45/0.54  % (27106)------------------------------
% 1.45/0.54  % (27106)------------------------------
% 1.45/0.54  % (27104)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.54  % (27087)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.45/0.54  % (27098)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.54  % (27096)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.58/0.59  % (27104)Refutation found. Thanks to Tanya!
% 1.58/0.59  % SZS status Theorem for theBenchmark
% 1.58/0.61  % (27169)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 1.58/0.61  % SZS output start Proof for theBenchmark
% 1.58/0.61  fof(f591,plain,(
% 1.58/0.61    $false),
% 1.58/0.61    inference(resolution,[],[f570,f191])).
% 1.58/0.61  fof(f191,plain,(
% 1.58/0.61    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 1.58/0.61    inference(unit_resulting_resolution,[],[f80,f77])).
% 1.58/0.61  fof(f77,plain,(
% 1.58/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | ~sP4(X4,X2,X1,X0)) )),
% 1.58/0.61    inference(equality_resolution,[],[f75])).
% 1.58/0.61  fof(f75,plain,(
% 1.58/0.61    ( ! [X4,X2,X0,X3,X1] : (~sP4(X4,X2,X1,X0) | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.58/0.61    inference(definition_unfolding,[],[f49,f60])).
% 1.58/0.61  fof(f60,plain,(
% 1.58/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.58/0.61    inference(definition_unfolding,[],[f42,f59])).
% 1.58/0.61  fof(f59,plain,(
% 1.58/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.58/0.61    inference(definition_unfolding,[],[f43,f58])).
% 1.58/0.61  fof(f58,plain,(
% 1.58/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.58/0.61    inference(definition_unfolding,[],[f53,f57])).
% 1.58/0.61  fof(f57,plain,(
% 1.58/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.58/0.61    inference(definition_unfolding,[],[f54,f55])).
% 1.58/0.61  fof(f55,plain,(
% 1.58/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f19])).
% 1.58/0.61  fof(f19,axiom,(
% 1.58/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.58/0.61  fof(f54,plain,(
% 1.58/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f18])).
% 1.58/0.61  fof(f18,axiom,(
% 1.58/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.58/0.61  fof(f53,plain,(
% 1.58/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f17])).
% 1.58/0.61  fof(f17,axiom,(
% 1.58/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.58/0.61  fof(f43,plain,(
% 1.58/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f16])).
% 1.58/0.61  fof(f16,axiom,(
% 1.58/0.61    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.58/0.61  fof(f42,plain,(
% 1.58/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f15])).
% 1.58/0.61  fof(f15,axiom,(
% 1.58/0.61    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.58/0.61  fof(f49,plain,(
% 1.58/0.61    ( ! [X4,X2,X0,X3,X1] : (~sP4(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.58/0.61    inference(cnf_transformation,[],[f26])).
% 1.58/0.61  fof(f26,plain,(
% 1.58/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.58/0.61    inference(ennf_transformation,[],[f9])).
% 1.58/0.61  fof(f9,axiom,(
% 1.58/0.61    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.58/0.61  fof(f80,plain,(
% 1.58/0.61    ( ! [X4,X2,X1] : (sP4(X4,X2,X1,X4)) )),
% 1.58/0.61    inference(equality_resolution,[],[f45])).
% 1.58/0.61  fof(f45,plain,(
% 1.58/0.61    ( ! [X4,X2,X0,X1] : (X0 != X4 | sP4(X4,X2,X1,X0)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f26])).
% 1.58/0.61  fof(f570,plain,(
% 1.58/0.61    ~r2_hidden(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2))),
% 1.58/0.61    inference(backward_demodulation,[],[f186,f563])).
% 1.58/0.61  fof(f563,plain,(
% 1.58/0.61    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 1.58/0.61    inference(superposition,[],[f548,f31])).
% 1.58/0.61  fof(f31,plain,(
% 1.58/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.58/0.61    inference(cnf_transformation,[],[f7])).
% 1.58/0.61  fof(f7,axiom,(
% 1.58/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.58/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.58/0.61  fof(f548,plain,(
% 1.58/0.61    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1,sK2)),
% 1.58/0.61    inference(forward_demodulation,[],[f547,f69])).
% 1.58/0.62  fof(f69,plain,(
% 1.58/0.62    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X2,X1)) )),
% 1.58/0.62    inference(definition_unfolding,[],[f40,f60,f60])).
% 1.58/0.62  fof(f40,plain,(
% 1.58/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 1.58/0.62    inference(cnf_transformation,[],[f20])).
% 1.58/0.62  fof(f20,axiom,(
% 1.58/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 1.58/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).
% 1.58/0.62  fof(f547,plain,(
% 1.58/0.62    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0) = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK2,sK1)),
% 1.58/0.62    inference(forward_demodulation,[],[f546,f213])).
% 1.58/0.62  fof(f213,plain,(
% 1.58/0.62    ( ! [X6,X8,X7] : (k6_enumset1(X6,X6,X6,X6,X6,X6,X8,X7) = k6_enumset1(X8,X8,X8,X8,X8,X8,X7,X6)) )),
% 1.58/0.62    inference(superposition,[],[f70,f69])).
% 1.58/0.62  fof(f70,plain,(
% 1.58/0.62    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0)) )),
% 1.58/0.62    inference(definition_unfolding,[],[f41,f60,f60])).
% 1.58/0.62  fof(f41,plain,(
% 1.58/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 1.58/0.62    inference(cnf_transformation,[],[f11])).
% 1.58/0.62  fof(f11,axiom,(
% 1.58/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 1.58/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_enumset1)).
% 1.58/0.62  fof(f546,plain,(
% 1.58/0.62    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK0,sK2)),
% 1.58/0.62    inference(forward_demodulation,[],[f535,f69])).
% 1.58/0.62  fof(f535,plain,(
% 1.58/0.62    k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0) = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK2,sK0)),
% 1.58/0.62    inference(superposition,[],[f71,f279])).
% 1.58/0.62  fof(f279,plain,(
% 1.58/0.62    k1_xboole_0 = k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.58/0.62    inference(unit_resulting_resolution,[],[f65,f151])).
% 1.58/0.62  fof(f151,plain,(
% 1.58/0.62    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,X2) | ~r1_tarski(X1,X2)) )),
% 1.58/0.62    inference(backward_demodulation,[],[f102,f145])).
% 1.58/0.62  fof(f145,plain,(
% 1.58/0.62    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(X7,X7)) )),
% 1.58/0.62    inference(backward_demodulation,[],[f131,f144])).
% 1.58/0.62  fof(f144,plain,(
% 1.58/0.62    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = X2) )),
% 1.58/0.62    inference(forward_demodulation,[],[f140,f31])).
% 1.58/0.62  fof(f140,plain,(
% 1.58/0.62    ( ! [X2] : (k4_xboole_0(X2,k1_xboole_0) = k5_xboole_0(X2,k1_xboole_0)) )),
% 1.58/0.62    inference(superposition,[],[f63,f131])).
% 1.58/0.62  fof(f63,plain,(
% 1.58/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.58/0.62    inference(definition_unfolding,[],[f37,f38])).
% 1.58/0.62  fof(f38,plain,(
% 1.58/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.58/0.62    inference(cnf_transformation,[],[f6])).
% 1.58/0.62  fof(f6,axiom,(
% 1.58/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.58/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.58/0.62  fof(f37,plain,(
% 1.58/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.58/0.62    inference(cnf_transformation,[],[f3])).
% 1.58/0.62  fof(f3,axiom,(
% 1.58/0.62    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.58/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.58/0.62  fof(f131,plain,(
% 1.58/0.62    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(X7,k4_xboole_0(X7,k1_xboole_0))) )),
% 1.58/0.62    inference(forward_demodulation,[],[f115,f85])).
% 1.58/0.62  fof(f85,plain,(
% 1.58/0.62    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.58/0.62    inference(superposition,[],[f81,f81])).
% 1.58/0.62  fof(f81,plain,(
% 1.58/0.62    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.58/0.62    inference(unit_resulting_resolution,[],[f30,f68])).
% 1.58/0.62  fof(f68,plain,(
% 1.58/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.58/0.62    inference(definition_unfolding,[],[f39,f38])).
% 1.58/0.62  fof(f39,plain,(
% 1.58/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.58/0.62    inference(cnf_transformation,[],[f25])).
% 1.58/0.62  fof(f25,plain,(
% 1.58/0.62    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.58/0.62    inference(ennf_transformation,[],[f4])).
% 1.58/0.62  fof(f4,axiom,(
% 1.58/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.58/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.58/0.62  fof(f30,plain,(
% 1.58/0.62    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.58/0.62    inference(cnf_transformation,[],[f5])).
% 1.58/0.62  fof(f5,axiom,(
% 1.58/0.62    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.58/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.58/0.62  fof(f115,plain,(
% 1.58/0.62    ( ! [X7] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X7,k4_xboole_0(X7,k1_xboole_0))) )),
% 1.58/0.62    inference(superposition,[],[f67,f103])).
% 1.58/0.62  fof(f103,plain,(
% 1.58/0.62    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X3)) )),
% 1.58/0.62    inference(forward_demodulation,[],[f101,f31])).
% 1.58/0.62  fof(f101,plain,(
% 1.58/0.62    ( ! [X3] : (k4_xboole_0(k1_xboole_0,X3) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.58/0.62    inference(superposition,[],[f63,f81])).
% 1.58/0.62  fof(f67,plain,(
% 1.58/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.58/0.62    inference(definition_unfolding,[],[f34,f38,f38])).
% 1.58/0.62  fof(f34,plain,(
% 1.58/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.58/0.62    inference(cnf_transformation,[],[f1])).
% 1.58/0.62  fof(f1,axiom,(
% 1.58/0.62    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.58/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.58/0.62  fof(f102,plain,(
% 1.58/0.62    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,X1) | ~r1_tarski(X1,X2)) )),
% 1.58/0.62    inference(forward_demodulation,[],[f100,f99])).
% 1.58/0.62  fof(f99,plain,(
% 1.58/0.62    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.58/0.62    inference(superposition,[],[f63,f66])).
% 1.58/0.62  fof(f66,plain,(
% 1.58/0.62    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.58/0.62    inference(definition_unfolding,[],[f33,f38])).
% 1.58/0.62  fof(f33,plain,(
% 1.58/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.58/0.62    inference(cnf_transformation,[],[f23])).
% 1.58/0.62  fof(f23,plain,(
% 1.58/0.62    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.58/0.62    inference(rectify,[],[f2])).
% 1.58/0.62  fof(f2,axiom,(
% 1.58/0.62    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.58/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.58/0.62  fof(f100,plain,(
% 1.58/0.62    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1) | ~r1_tarski(X1,X2)) )),
% 1.58/0.62    inference(superposition,[],[f63,f68])).
% 1.58/0.62  fof(f65,plain,(
% 1.58/0.62    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.58/0.62    inference(definition_unfolding,[],[f27,f62,f61])).
% 1.58/0.62  fof(f61,plain,(
% 1.58/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.58/0.62    inference(definition_unfolding,[],[f35,f60])).
% 1.58/0.62  fof(f35,plain,(
% 1.58/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.58/0.62    inference(cnf_transformation,[],[f14])).
% 1.58/0.62  fof(f14,axiom,(
% 1.58/0.62    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.58/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.58/0.62  fof(f62,plain,(
% 1.58/0.62    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.58/0.62    inference(definition_unfolding,[],[f32,f61])).
% 1.58/0.62  fof(f32,plain,(
% 1.58/0.62    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.58/0.62    inference(cnf_transformation,[],[f13])).
% 1.58/0.62  fof(f13,axiom,(
% 1.58/0.62    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.58/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.58/0.62  fof(f27,plain,(
% 1.58/0.62    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.58/0.62    inference(cnf_transformation,[],[f24])).
% 1.58/0.62  fof(f24,plain,(
% 1.58/0.62    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.58/0.62    inference(ennf_transformation,[],[f22])).
% 1.58/0.62  fof(f22,negated_conjecture,(
% 1.58/0.62    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.58/0.62    inference(negated_conjecture,[],[f21])).
% 1.58/0.62  fof(f21,conjecture,(
% 1.58/0.62    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.58/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.58/0.62  fof(f71,plain,(
% 1.58/0.62    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2),k4_xboole_0(k6_enumset1(X3,X3,X3,X3,X3,X3,X3,X3),k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)))) )),
% 1.58/0.62    inference(definition_unfolding,[],[f44,f59,f36,f60,f62])).
% 1.58/0.62  fof(f36,plain,(
% 1.58/0.62    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.58/0.62    inference(cnf_transformation,[],[f8])).
% 1.58/0.62  fof(f8,axiom,(
% 1.58/0.62    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.58/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.58/0.62  fof(f44,plain,(
% 1.58/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.58/0.62    inference(cnf_transformation,[],[f12])).
% 1.58/0.62  fof(f12,axiom,(
% 1.58/0.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.58/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).
% 1.58/0.62  fof(f186,plain,(
% 1.58/0.62    ~r2_hidden(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.58/0.62    inference(forward_demodulation,[],[f185,f70])).
% 1.58/0.62  fof(f185,plain,(
% 1.58/0.62    ~r2_hidden(sK0,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1,sK1))),
% 1.58/0.62    inference(unit_resulting_resolution,[],[f160,f76])).
% 1.58/0.62  fof(f76,plain,(
% 1.58/0.62    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | sP4(X4,X2,X1,X0)) )),
% 1.58/0.62    inference(equality_resolution,[],[f74])).
% 1.58/0.62  fof(f74,plain,(
% 1.58/0.62    ( ! [X4,X2,X0,X3,X1] : (sP4(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.58/0.62    inference(definition_unfolding,[],[f50,f60])).
% 1.58/0.62  fof(f50,plain,(
% 1.58/0.62    ( ! [X4,X2,X0,X3,X1] : (sP4(X4,X2,X1,X0) | ~r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.58/0.62    inference(cnf_transformation,[],[f26])).
% 1.58/0.62  fof(f160,plain,(
% 1.58/0.62    ~sP4(sK0,sK1,sK1,sK2)),
% 1.58/0.62    inference(unit_resulting_resolution,[],[f29,f28,f28,f48])).
% 1.58/0.62  fof(f48,plain,(
% 1.58/0.62    ( ! [X4,X2,X0,X1] : (~sP4(X4,X2,X1,X0) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.58/0.62    inference(cnf_transformation,[],[f26])).
% 1.58/0.62  fof(f28,plain,(
% 1.58/0.62    sK0 != sK1),
% 1.58/0.62    inference(cnf_transformation,[],[f24])).
% 1.58/0.62  fof(f29,plain,(
% 1.58/0.62    sK0 != sK2),
% 1.58/0.62    inference(cnf_transformation,[],[f24])).
% 1.58/0.62  % SZS output end Proof for theBenchmark
% 1.58/0.62  % (27104)------------------------------
% 1.58/0.62  % (27104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.62  % (27104)Termination reason: Refutation
% 1.58/0.62  
% 1.58/0.62  % (27104)Memory used [KB]: 6780
% 1.58/0.62  % (27104)Time elapsed: 0.179 s
% 1.58/0.62  % (27104)------------------------------
% 1.58/0.62  % (27104)------------------------------
% 1.58/0.62  % (27079)Success in time 0.257 s
%------------------------------------------------------------------------------

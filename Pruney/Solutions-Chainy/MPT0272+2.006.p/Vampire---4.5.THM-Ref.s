%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:12 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 361 expanded)
%              Number of leaves         :   18 ( 116 expanded)
%              Depth                    :   16
%              Number of atoms          :  122 ( 476 expanded)
%              Number of equality atoms :   70 ( 382 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f891,plain,(
    $false ),
    inference(resolution,[],[f874,f77])).

fof(f77,plain,(
    ! [X4,X2,X0] : sP3(X4,X2,X4,X0) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 != X4
      | sP3(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f874,plain,(
    ~ sP3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f302,f863])).

fof(f863,plain,(
    ! [X0,X1] : k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK0))) ),
    inference(unit_resulting_resolution,[],[f824,f824,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f61,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,X1)
      | k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f824,plain,(
    ! [X0,X1] : r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK0))) ),
    inference(forward_demodulation,[],[f801,f30])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f801,plain,(
    ! [X0,X1] : r2_hidden(sK0,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f243,f379,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f379,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f76,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | ~ sP3(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP3(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f50,f60])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP3(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f76,plain,(
    ! [X4,X0,X1] : sP3(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP3(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f243,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f128,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f61])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f128,plain,(
    ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f79,f85])).

fof(f85,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X2,X1))
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f68,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f36,f33])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f79,plain,(
    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f64,f31])).

fof(f64,plain,(
    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f26,f33,f62])).

fof(f26,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f302,plain,(
    ~ sP3(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f301,f30])).

fof(f301,plain,(
    ~ sP3(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f274,f154])).

fof(f154,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f134,f31])).

fof(f134,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f39,f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f274,plain,(
    ~ sP3(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f79,f79,f80,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X4,X2,X1,X0)
      | X1 = X4
      | X2 = X4
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f63,f31])).

fof(f63,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(definition_unfolding,[],[f27,f62,f33,f62])).

fof(f27,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:32:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.49  % (30130)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (30141)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.50  % (30135)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.50  % (30133)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.50  % (30126)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.51  % (30147)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (30148)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (30138)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (30154)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.23/0.52  % (30131)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.23/0.52  % (30140)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.23/0.52  % (30146)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.23/0.52  % (30147)Refutation not found, incomplete strategy% (30147)------------------------------
% 1.23/0.52  % (30147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (30147)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.52  
% 1.23/0.52  % (30147)Memory used [KB]: 1663
% 1.23/0.52  % (30147)Time elapsed: 0.111 s
% 1.23/0.52  % (30147)------------------------------
% 1.23/0.52  % (30147)------------------------------
% 1.23/0.52  % (30155)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.23/0.52  % (30132)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.23/0.53  % (30129)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.23/0.53  % (30151)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.23/0.53  % (30149)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.23/0.54  % (30127)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.23/0.54  % (30128)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.54  % (30128)Refutation not found, incomplete strategy% (30128)------------------------------
% 1.23/0.54  % (30128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (30128)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (30128)Memory used [KB]: 10618
% 1.23/0.54  % (30128)Time elapsed: 0.126 s
% 1.23/0.54  % (30128)------------------------------
% 1.23/0.54  % (30128)------------------------------
% 1.23/0.54  % (30137)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.23/0.54  % (30144)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.23/0.54  % (30143)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.23/0.54  % (30153)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.54  % (30142)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.54  % (30146)Refutation not found, incomplete strategy% (30146)------------------------------
% 1.45/0.54  % (30146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (30146)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.54  
% 1.45/0.54  % (30146)Memory used [KB]: 10746
% 1.45/0.54  % (30146)Time elapsed: 0.113 s
% 1.45/0.54  % (30146)------------------------------
% 1.45/0.54  % (30146)------------------------------
% 1.45/0.55  % (30136)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.55  % (30145)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.55  % (30143)Refutation not found, incomplete strategy% (30143)------------------------------
% 1.45/0.55  % (30143)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (30136)Refutation not found, incomplete strategy% (30136)------------------------------
% 1.45/0.55  % (30136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (30136)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (30136)Memory used [KB]: 10618
% 1.45/0.55  % (30136)Time elapsed: 0.140 s
% 1.45/0.55  % (30136)------------------------------
% 1.45/0.55  % (30136)------------------------------
% 1.45/0.55  % (30143)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (30143)Memory used [KB]: 10746
% 1.45/0.55  % (30143)Time elapsed: 0.141 s
% 1.45/0.55  % (30143)------------------------------
% 1.45/0.55  % (30143)------------------------------
% 1.45/0.55  % (30134)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.55  % (30134)Refutation not found, incomplete strategy% (30134)------------------------------
% 1.45/0.55  % (30134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (30134)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (30134)Memory used [KB]: 10618
% 1.45/0.55  % (30134)Time elapsed: 0.138 s
% 1.45/0.55  % (30134)------------------------------
% 1.45/0.55  % (30134)------------------------------
% 1.45/0.55  % (30150)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.55  % (30139)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.56  % (30137)Refutation not found, incomplete strategy% (30137)------------------------------
% 1.45/0.56  % (30137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (30137)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (30137)Memory used [KB]: 10618
% 1.45/0.56  % (30137)Time elapsed: 0.151 s
% 1.45/0.56  % (30137)------------------------------
% 1.45/0.56  % (30137)------------------------------
% 1.45/0.56  % (30152)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.62  % (30150)Refutation found. Thanks to Tanya!
% 1.45/0.62  % SZS status Theorem for theBenchmark
% 1.45/0.63  % SZS output start Proof for theBenchmark
% 1.45/0.63  fof(f891,plain,(
% 1.45/0.63    $false),
% 1.45/0.63    inference(resolution,[],[f874,f77])).
% 1.45/0.63  fof(f77,plain,(
% 1.45/0.63    ( ! [X4,X2,X0] : (sP3(X4,X2,X4,X0)) )),
% 1.45/0.63    inference(equality_resolution,[],[f47])).
% 1.45/0.63  fof(f47,plain,(
% 1.45/0.63    ( ! [X4,X2,X0,X1] : (X1 != X4 | sP3(X4,X2,X1,X0)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f25])).
% 1.45/0.63  fof(f25,plain,(
% 1.45/0.63    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.45/0.63    inference(ennf_transformation,[],[f8])).
% 1.45/0.63  fof(f8,axiom,(
% 1.45/0.63    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.45/0.63  fof(f874,plain,(
% 1.45/0.63    ~sP3(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.45/0.63    inference(backward_demodulation,[],[f302,f863])).
% 1.45/0.63  fof(f863,plain,(
% 1.45/0.63    ( ! [X0,X1] : (k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK0)))) )),
% 1.45/0.63    inference(unit_resulting_resolution,[],[f824,f824,f69])).
% 1.45/0.63  fof(f69,plain,(
% 1.45/0.63    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2) = k3_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)) )),
% 1.45/0.63    inference(definition_unfolding,[],[f40,f61,f61])).
% 1.45/0.63  fof(f61,plain,(
% 1.45/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.45/0.63    inference(definition_unfolding,[],[f32,f60])).
% 1.45/0.63  fof(f60,plain,(
% 1.45/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.45/0.63    inference(definition_unfolding,[],[f38,f59])).
% 1.45/0.63  fof(f59,plain,(
% 1.45/0.63    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.45/0.63    inference(definition_unfolding,[],[f45,f58])).
% 1.45/0.63  fof(f58,plain,(
% 1.45/0.63    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.45/0.63    inference(definition_unfolding,[],[f54,f57])).
% 1.45/0.63  fof(f57,plain,(
% 1.45/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.45/0.63    inference(definition_unfolding,[],[f55,f56])).
% 1.45/0.63  fof(f56,plain,(
% 1.45/0.63    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f15])).
% 1.45/0.63  fof(f15,axiom,(
% 1.45/0.63    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.45/0.63  fof(f55,plain,(
% 1.45/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f14])).
% 1.45/0.63  fof(f14,axiom,(
% 1.45/0.63    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.45/0.63  fof(f54,plain,(
% 1.45/0.63    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f13])).
% 1.45/0.63  fof(f13,axiom,(
% 1.45/0.63    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.45/0.63  fof(f45,plain,(
% 1.45/0.63    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f12])).
% 1.45/0.63  fof(f12,axiom,(
% 1.45/0.63    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.45/0.63  fof(f38,plain,(
% 1.45/0.63    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f11])).
% 1.45/0.63  fof(f11,axiom,(
% 1.45/0.63    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.45/0.63  fof(f32,plain,(
% 1.45/0.63    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f10])).
% 1.45/0.63  fof(f10,axiom,(
% 1.45/0.63    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.45/0.63  fof(f40,plain,(
% 1.45/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X2,X1) | k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f23])).
% 1.45/0.63  fof(f23,plain,(
% 1.45/0.63    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 1.45/0.63    inference(flattening,[],[f22])).
% 1.45/0.63  fof(f22,plain,(
% 1.45/0.63    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 1.45/0.63    inference(ennf_transformation,[],[f17])).
% 1.45/0.63  fof(f17,axiom,(
% 1.45/0.63    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 1.45/0.63  fof(f824,plain,(
% 1.45/0.63    ( ! [X0,X1] : (r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK0)))) )),
% 1.45/0.63    inference(forward_demodulation,[],[f801,f30])).
% 1.45/0.63  fof(f30,plain,(
% 1.45/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f2])).
% 1.45/0.63  fof(f2,axiom,(
% 1.45/0.63    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.45/0.63  fof(f801,plain,(
% 1.45/0.63    ( ! [X0,X1] : (r2_hidden(sK0,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X1,sK0),sK1))) )),
% 1.45/0.63    inference(unit_resulting_resolution,[],[f243,f379,f44])).
% 1.45/0.63  fof(f44,plain,(
% 1.45/0.63    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f24])).
% 1.45/0.63  fof(f24,plain,(
% 1.45/0.63    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.45/0.63    inference(ennf_transformation,[],[f4])).
% 1.45/0.63  fof(f4,axiom,(
% 1.45/0.63    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.45/0.63  fof(f379,plain,(
% 1.45/0.63    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))) )),
% 1.45/0.63    inference(unit_resulting_resolution,[],[f76,f75])).
% 1.45/0.63  fof(f75,plain,(
% 1.45/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | ~sP3(X4,X2,X1,X0)) )),
% 1.45/0.63    inference(equality_resolution,[],[f73])).
% 1.45/0.63  fof(f73,plain,(
% 1.45/0.63    ( ! [X4,X2,X0,X3,X1] : (~sP3(X4,X2,X1,X0) | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.45/0.63    inference(definition_unfolding,[],[f50,f60])).
% 1.45/0.63  fof(f50,plain,(
% 1.45/0.63    ( ! [X4,X2,X0,X3,X1] : (~sP3(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.45/0.63    inference(cnf_transformation,[],[f25])).
% 1.45/0.63  fof(f76,plain,(
% 1.45/0.63    ( ! [X4,X0,X1] : (sP3(X4,X4,X1,X0)) )),
% 1.45/0.63    inference(equality_resolution,[],[f48])).
% 1.45/0.63  fof(f48,plain,(
% 1.45/0.63    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP3(X4,X2,X1,X0)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f25])).
% 1.45/0.63  fof(f243,plain,(
% 1.45/0.63    ~r2_hidden(sK0,sK1)),
% 1.45/0.63    inference(unit_resulting_resolution,[],[f128,f66])).
% 1.45/0.63  fof(f66,plain,(
% 1.45/0.63    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.45/0.63    inference(definition_unfolding,[],[f34,f62])).
% 1.45/0.63  fof(f62,plain,(
% 1.45/0.63    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.45/0.63    inference(definition_unfolding,[],[f28,f61])).
% 1.45/0.63  fof(f28,plain,(
% 1.45/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f9])).
% 1.45/0.63  fof(f9,axiom,(
% 1.45/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.45/0.63  fof(f34,plain,(
% 1.45/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f16])).
% 1.45/0.63  fof(f16,axiom,(
% 1.45/0.63    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.45/0.63  fof(f128,plain,(
% 1.45/0.63    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 1.45/0.63    inference(unit_resulting_resolution,[],[f79,f85])).
% 1.45/0.63  fof(f85,plain,(
% 1.45/0.63    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k3_xboole_0(X2,X1)) | ~r1_tarski(X1,X2)) )),
% 1.45/0.63    inference(superposition,[],[f68,f31])).
% 1.45/0.63  fof(f31,plain,(
% 1.45/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f1])).
% 1.45/0.63  fof(f1,axiom,(
% 1.45/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.45/0.63  fof(f68,plain,(
% 1.45/0.63    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 1.45/0.63    inference(definition_unfolding,[],[f36,f33])).
% 1.45/0.63  fof(f33,plain,(
% 1.45/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.45/0.63    inference(cnf_transformation,[],[f6])).
% 1.45/0.63  fof(f6,axiom,(
% 1.45/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.45/0.63  fof(f36,plain,(
% 1.45/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.45/0.63    inference(cnf_transformation,[],[f5])).
% 1.45/0.63  fof(f5,axiom,(
% 1.45/0.63    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.45/0.63  fof(f79,plain,(
% 1.45/0.63    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.45/0.63    inference(backward_demodulation,[],[f64,f31])).
% 1.45/0.63  fof(f64,plain,(
% 1.45/0.63    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.45/0.63    inference(definition_unfolding,[],[f26,f33,f62])).
% 1.45/0.63  fof(f26,plain,(
% 1.45/0.63    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.45/0.63    inference(cnf_transformation,[],[f21])).
% 1.45/0.63  fof(f21,plain,(
% 1.45/0.63    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 1.45/0.63    inference(ennf_transformation,[],[f19])).
% 1.45/0.63  fof(f19,negated_conjecture,(
% 1.45/0.63    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 1.45/0.63    inference(negated_conjecture,[],[f18])).
% 1.45/0.63  fof(f18,conjecture,(
% 1.45/0.63    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 1.45/0.63  fof(f302,plain,(
% 1.45/0.63    ~sP3(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.45/0.63    inference(forward_demodulation,[],[f301,f30])).
% 1.45/0.63  fof(f301,plain,(
% 1.45/0.63    ~sP3(k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.45/0.63    inference(forward_demodulation,[],[f274,f154])).
% 1.45/0.63  fof(f154,plain,(
% 1.45/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.45/0.63    inference(forward_demodulation,[],[f134,f31])).
% 1.45/0.63  fof(f134,plain,(
% 1.45/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 1.45/0.63    inference(superposition,[],[f39,f29])).
% 1.45/0.63  fof(f29,plain,(
% 1.45/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.45/0.63    inference(cnf_transformation,[],[f20])).
% 1.45/0.63  fof(f20,plain,(
% 1.45/0.63    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.45/0.63    inference(rectify,[],[f3])).
% 1.45/0.63  fof(f3,axiom,(
% 1.45/0.63    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.45/0.63  fof(f39,plain,(
% 1.45/0.63    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.45/0.63    inference(cnf_transformation,[],[f7])).
% 1.45/0.63  fof(f7,axiom,(
% 1.45/0.63    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.45/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.45/0.63  fof(f274,plain,(
% 1.45/0.63    ~sP3(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),
% 1.45/0.63    inference(unit_resulting_resolution,[],[f79,f79,f80,f49])).
% 1.45/0.63  fof(f49,plain,(
% 1.45/0.63    ( ! [X4,X2,X0,X1] : (~sP3(X4,X2,X1,X0) | X1 = X4 | X2 = X4 | X0 = X4) )),
% 1.45/0.63    inference(cnf_transformation,[],[f25])).
% 1.45/0.63  fof(f80,plain,(
% 1.45/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 1.45/0.63    inference(backward_demodulation,[],[f63,f31])).
% 1.45/0.63  fof(f63,plain,(
% 1.45/0.63    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 1.45/0.63    inference(definition_unfolding,[],[f27,f62,f33,f62])).
% 1.45/0.63  fof(f27,plain,(
% 1.45/0.63    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.45/0.63    inference(cnf_transformation,[],[f21])).
% 1.45/0.63  % SZS output end Proof for theBenchmark
% 1.45/0.63  % (30150)------------------------------
% 1.45/0.63  % (30150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.63  % (30150)Termination reason: Refutation
% 1.45/0.63  
% 1.45/0.63  % (30150)Memory used [KB]: 7036
% 1.45/0.63  % (30150)Time elapsed: 0.208 s
% 1.45/0.63  % (30150)------------------------------
% 1.45/0.63  % (30150)------------------------------
% 1.45/0.63  % (30125)Success in time 0.264 s
%------------------------------------------------------------------------------

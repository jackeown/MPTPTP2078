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
% DateTime   : Thu Dec  3 12:38:01 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :  115 (1706 expanded)
%              Number of leaves         :   23 ( 556 expanded)
%              Depth                    :   22
%              Number of atoms          :  210 (2234 expanded)
%              Number of equality atoms :  125 (1980 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f661,plain,(
    $false ),
    inference(global_subsumption,[],[f645,f656])).

fof(f656,plain,(
    ~ r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f307,f654,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f654,plain,(
    ~ v1_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f653,f48])).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f653,plain,(
    ~ v1_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2)) ),
    inference(unit_resulting_resolution,[],[f644,f157])).

fof(f157,plain,(
    ! [X4,X5] :
      ( ~ v1_xboole_0(k5_xboole_0(X4,X5))
      | X4 = X5 ) ),
    inference(superposition,[],[f145,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X1,X0) = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f39,f43])).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f39,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f145,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f125,f88])).

fof(f88,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f87,f78])).

fof(f78,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f45,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f69])).

fof(f69,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f59,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f62,f65])).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f63,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f87,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(forward_demodulation,[],[f77,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f77,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f44,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f70])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f125,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f60,f38])).

fof(f60,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f644,plain,(
    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(global_subsumption,[],[f75,f629])).

fof(f629,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f357,f356,f625])).

fof(f625,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f624])).

fof(f624,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f350,f366])).

fof(f366,plain,
    ( r1_tarski(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f365,f145])).

fof(f365,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f360,f137])).

fof(f137,plain,(
    ! [X14,X15,X13] : k5_xboole_0(X13,k5_xboole_0(X14,X15)) = k5_xboole_0(X15,k5_xboole_0(X13,X14)) ),
    inference(superposition,[],[f60,f48])).

fof(f360,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f287,f341])).

fof(f341,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f83,f272])).

fof(f272,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f79,f73])).

fof(f73,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f37,f72,f70])).

fof(f72,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f40,f69])).

fof(f40,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f37,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f79,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f46,f70])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f56,f72,f72])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f287,plain,(
    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(superposition,[],[f89,f73])).

fof(f89,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(backward_demodulation,[],[f80,f60])).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f47,f71])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f350,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK1 = X0
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f83,f341])).

fof(f356,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f346])).

fof(f346,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f76,f341])).

fof(f76,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f34,f72])).

fof(f34,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f357,plain,
    ( sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f344])).

fof(f344,plain,
    ( sK1 != sK2
    | sK1 != sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f74,f341])).

fof(f74,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f36,f72,f72])).

fof(f36,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f35,f72])).

fof(f35,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f307,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f301,f266])).

fof(f266,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f265])).

fof(f265,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f123,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X2)
      | ~ r1_xboole_0(X2,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f301,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f84,f267])).

fof(f267,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f264])).

fof(f264,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f123,f53])).

fof(f84,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( r1_xboole_0(X0,X0)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f645,plain,(
    r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f635,f88])).

fof(f635,plain,(
    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) ),
    inference(backward_demodulation,[],[f287,f629])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n018.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:42:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.54  % (18333)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (18327)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.55  % (18343)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (18333)Refutation not found, incomplete strategy% (18333)------------------------------
% 0.22/0.55  % (18333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (18333)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (18333)Memory used [KB]: 10618
% 0.22/0.55  % (18333)Time elapsed: 0.122 s
% 0.22/0.55  % (18333)------------------------------
% 0.22/0.55  % (18333)------------------------------
% 0.22/0.55  % (18328)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (18325)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.56  % (18325)Refutation not found, incomplete strategy% (18325)------------------------------
% 0.22/0.56  % (18325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (18325)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (18325)Memory used [KB]: 10746
% 0.22/0.56  % (18325)Time elapsed: 0.121 s
% 0.22/0.56  % (18325)------------------------------
% 0.22/0.56  % (18325)------------------------------
% 0.22/0.56  % (18323)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.57  % (18351)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.57  % (18335)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (18344)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.58  % (18336)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.58  % (18334)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.58  % (18344)Refutation not found, incomplete strategy% (18344)------------------------------
% 0.22/0.58  % (18344)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (18334)Refutation not found, incomplete strategy% (18334)------------------------------
% 1.63/0.58  % (18334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (18334)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (18334)Memory used [KB]: 10618
% 1.63/0.58  % (18334)Time elapsed: 0.153 s
% 1.63/0.58  % (18334)------------------------------
% 1.63/0.58  % (18334)------------------------------
% 1.63/0.58  % (18344)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (18344)Memory used [KB]: 1791
% 1.63/0.58  % (18344)Time elapsed: 0.145 s
% 1.63/0.58  % (18344)------------------------------
% 1.63/0.58  % (18344)------------------------------
% 1.63/0.59  % (18329)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.63/0.60  % (18324)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.63/0.60  % (18330)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.63/0.60  % (18326)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.63/0.60  % (18345)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.87/0.61  % (18341)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.87/0.61  % (18338)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.87/0.61  % (18338)Refutation not found, incomplete strategy% (18338)------------------------------
% 1.87/0.61  % (18338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.61  % (18338)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.61  
% 1.87/0.61  % (18338)Memory used [KB]: 6140
% 1.87/0.61  % (18338)Time elapsed: 0.002 s
% 1.87/0.61  % (18338)------------------------------
% 1.87/0.61  % (18338)------------------------------
% 1.87/0.61  % (18349)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.87/0.61  % (18352)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.87/0.61  % (18347)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.87/0.61  % (18350)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.87/0.61  % (18348)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.87/0.62  % (18339)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.87/0.62  % (18337)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.87/0.62  % (18342)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.87/0.62  % (18332)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.87/0.62  % (18346)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.87/0.63  % (18340)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.87/0.63  % (18331)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.87/0.63  % (18340)Refutation not found, incomplete strategy% (18340)------------------------------
% 1.87/0.63  % (18340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.63  % (18340)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.63  
% 1.87/0.63  % (18340)Memory used [KB]: 10618
% 1.87/0.63  % (18340)Time elapsed: 0.204 s
% 1.87/0.63  % (18340)------------------------------
% 1.87/0.63  % (18340)------------------------------
% 1.87/0.63  % (18331)Refutation not found, incomplete strategy% (18331)------------------------------
% 1.87/0.63  % (18331)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.63  % (18331)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.63  
% 1.87/0.63  % (18331)Memory used [KB]: 10746
% 1.87/0.63  % (18331)Time elapsed: 0.203 s
% 1.87/0.63  % (18331)------------------------------
% 1.87/0.63  % (18331)------------------------------
% 1.87/0.65  % (18345)Refutation not found, incomplete strategy% (18345)------------------------------
% 1.87/0.65  % (18345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.87/0.65  % (18345)Termination reason: Refutation not found, incomplete strategy
% 1.87/0.65  
% 1.87/0.65  % (18345)Memory used [KB]: 10874
% 1.87/0.65  % (18345)Time elapsed: 0.214 s
% 1.87/0.65  % (18345)------------------------------
% 1.87/0.65  % (18345)------------------------------
% 2.20/0.66  % (18347)Refutation found. Thanks to Tanya!
% 2.20/0.66  % SZS status Theorem for theBenchmark
% 2.20/0.66  % SZS output start Proof for theBenchmark
% 2.20/0.66  fof(f661,plain,(
% 2.20/0.66    $false),
% 2.20/0.66    inference(global_subsumption,[],[f645,f656])).
% 2.20/0.66  fof(f656,plain,(
% 2.20/0.66    ~r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 2.20/0.66    inference(unit_resulting_resolution,[],[f307,f654,f55])).
% 2.20/0.66  fof(f55,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_xboole_0(X1) | ~r1_xboole_0(X1,X0)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f33])).
% 2.20/0.66  fof(f33,plain,(
% 2.20/0.66    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.20/0.66    inference(flattening,[],[f32])).
% 2.20/0.66  fof(f32,plain,(
% 2.20/0.66    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.20/0.66    inference(ennf_transformation,[],[f9])).
% 2.20/0.66  fof(f9,axiom,(
% 2.20/0.66    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 2.20/0.66  fof(f654,plain,(
% 2.20/0.66    ~v1_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.20/0.66    inference(forward_demodulation,[],[f653,f48])).
% 2.20/0.66  fof(f48,plain,(
% 2.20/0.66    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f1])).
% 2.20/0.66  fof(f1,axiom,(
% 2.20/0.66    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.20/0.66  fof(f653,plain,(
% 2.20/0.66    ~v1_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2))),
% 2.20/0.66    inference(unit_resulting_resolution,[],[f644,f157])).
% 2.20/0.66  fof(f157,plain,(
% 2.20/0.66    ( ! [X4,X5] : (~v1_xboole_0(k5_xboole_0(X4,X5)) | X4 = X5) )),
% 2.20/0.66    inference(superposition,[],[f145,f91])).
% 2.20/0.66  fof(f91,plain,(
% 2.20/0.66    ( ! [X0,X1] : (k5_xboole_0(X1,X0) = X1 | ~v1_xboole_0(X0)) )),
% 2.20/0.66    inference(superposition,[],[f39,f43])).
% 2.20/0.66  fof(f43,plain,(
% 2.20/0.66    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f30])).
% 2.20/0.66  fof(f30,plain,(
% 2.20/0.66    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.20/0.66    inference(ennf_transformation,[],[f4])).
% 2.20/0.66  fof(f4,axiom,(
% 2.20/0.66    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 2.20/0.66  fof(f39,plain,(
% 2.20/0.66    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.20/0.66    inference(cnf_transformation,[],[f7])).
% 2.20/0.66  fof(f7,axiom,(
% 2.20/0.66    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.20/0.66  fof(f145,plain,(
% 2.20/0.66    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.20/0.66    inference(forward_demodulation,[],[f125,f88])).
% 2.20/0.66  fof(f88,plain,(
% 2.20/0.66    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.20/0.66    inference(backward_demodulation,[],[f87,f78])).
% 2.20/0.66  fof(f78,plain,(
% 2.20/0.66    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.20/0.66    inference(definition_unfolding,[],[f45,f70])).
% 2.20/0.66  fof(f70,plain,(
% 2.20/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.20/0.66    inference(definition_unfolding,[],[f49,f69])).
% 2.20/0.66  fof(f69,plain,(
% 2.20/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.20/0.66    inference(definition_unfolding,[],[f50,f68])).
% 2.20/0.66  fof(f68,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.20/0.66    inference(definition_unfolding,[],[f59,f67])).
% 2.20/0.66  fof(f67,plain,(
% 2.20/0.66    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.20/0.66    inference(definition_unfolding,[],[f61,f66])).
% 2.20/0.66  fof(f66,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.20/0.66    inference(definition_unfolding,[],[f62,f65])).
% 2.20/0.66  fof(f65,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.20/0.66    inference(definition_unfolding,[],[f63,f64])).
% 2.20/0.66  fof(f64,plain,(
% 2.20/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f20])).
% 2.20/0.66  fof(f20,axiom,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.20/0.66  fof(f63,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f19])).
% 2.20/0.66  fof(f19,axiom,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.20/0.66  fof(f62,plain,(
% 2.20/0.66    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f18])).
% 2.20/0.66  fof(f18,axiom,(
% 2.20/0.66    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.20/0.66  fof(f61,plain,(
% 2.20/0.66    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f17])).
% 2.20/0.66  fof(f17,axiom,(
% 2.20/0.66    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.20/0.66  fof(f59,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f16])).
% 2.20/0.66  fof(f16,axiom,(
% 2.20/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.20/0.66  fof(f50,plain,(
% 2.20/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f15])).
% 2.20/0.66  fof(f15,axiom,(
% 2.20/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.20/0.66  fof(f49,plain,(
% 2.20/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.20/0.66    inference(cnf_transformation,[],[f22])).
% 2.20/0.66  fof(f22,axiom,(
% 2.20/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.20/0.66  fof(f45,plain,(
% 2.20/0.66    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.20/0.66    inference(cnf_transformation,[],[f26])).
% 2.20/0.66  fof(f26,plain,(
% 2.20/0.66    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.20/0.66    inference(rectify,[],[f2])).
% 2.20/0.66  fof(f2,axiom,(
% 2.20/0.66    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.20/0.66  fof(f87,plain,(
% 2.20/0.66    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 2.20/0.66    inference(forward_demodulation,[],[f77,f38])).
% 2.20/0.66  fof(f38,plain,(
% 2.20/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f12])).
% 2.20/0.66  fof(f12,axiom,(
% 2.20/0.66    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.20/0.66  fof(f77,plain,(
% 2.20/0.66    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 2.20/0.66    inference(definition_unfolding,[],[f44,f71])).
% 2.20/0.66  fof(f71,plain,(
% 2.20/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.20/0.66    inference(definition_unfolding,[],[f51,f70])).
% 2.20/0.66  fof(f51,plain,(
% 2.20/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.20/0.66    inference(cnf_transformation,[],[f13])).
% 2.20/0.66  fof(f13,axiom,(
% 2.20/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.20/0.66  fof(f44,plain,(
% 2.20/0.66    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.20/0.66    inference(cnf_transformation,[],[f25])).
% 2.20/0.66  fof(f25,plain,(
% 2.20/0.66    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.20/0.66    inference(rectify,[],[f3])).
% 2.20/0.66  fof(f3,axiom,(
% 2.20/0.66    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.20/0.66  fof(f125,plain,(
% 2.20/0.66    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.20/0.66    inference(superposition,[],[f60,f38])).
% 2.20/0.66  fof(f60,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.20/0.66    inference(cnf_transformation,[],[f11])).
% 2.20/0.66  fof(f11,axiom,(
% 2.20/0.66    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.20/0.66  fof(f644,plain,(
% 2.20/0.66    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.20/0.66    inference(global_subsumption,[],[f75,f629])).
% 2.20/0.66  fof(f629,plain,(
% 2.20/0.66    k1_xboole_0 = sK1),
% 2.20/0.66    inference(global_subsumption,[],[f357,f356,f625])).
% 2.20/0.66  fof(f625,plain,(
% 2.20/0.66    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 2.20/0.66    inference(duplicate_literal_removal,[],[f624])).
% 2.20/0.66  fof(f624,plain,(
% 2.20/0.66    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 2.20/0.66    inference(resolution,[],[f350,f366])).
% 2.20/0.66  fof(f366,plain,(
% 2.20/0.66    r1_tarski(sK2,sK1) | k1_xboole_0 = sK1),
% 2.20/0.66    inference(forward_demodulation,[],[f365,f145])).
% 2.20/0.66  fof(f365,plain,(
% 2.20/0.66    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1) | k1_xboole_0 = sK1),
% 2.20/0.66    inference(forward_demodulation,[],[f360,f137])).
% 2.20/0.66  fof(f137,plain,(
% 2.20/0.66    ( ! [X14,X15,X13] : (k5_xboole_0(X13,k5_xboole_0(X14,X15)) = k5_xboole_0(X15,k5_xboole_0(X13,X14))) )),
% 2.20/0.66    inference(superposition,[],[f60,f48])).
% 2.20/0.66  fof(f360,plain,(
% 2.20/0.66    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) | k1_xboole_0 = sK1),
% 2.20/0.66    inference(superposition,[],[f287,f341])).
% 2.20/0.66  fof(f341,plain,(
% 2.20/0.66    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1),
% 2.20/0.66    inference(resolution,[],[f83,f272])).
% 2.20/0.66  fof(f272,plain,(
% 2.20/0.66    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.20/0.66    inference(superposition,[],[f79,f73])).
% 2.20/0.66  fof(f73,plain,(
% 2.20/0.66    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.20/0.66    inference(definition_unfolding,[],[f37,f72,f70])).
% 2.20/0.66  fof(f72,plain,(
% 2.20/0.66    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.20/0.66    inference(definition_unfolding,[],[f40,f69])).
% 2.20/0.66  fof(f40,plain,(
% 2.20/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f14])).
% 2.20/0.66  fof(f14,axiom,(
% 2.20/0.66    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.20/0.66  fof(f37,plain,(
% 2.20/0.66    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.20/0.66    inference(cnf_transformation,[],[f28])).
% 2.20/0.66  fof(f28,plain,(
% 2.20/0.66    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.20/0.66    inference(ennf_transformation,[],[f24])).
% 2.20/0.66  fof(f24,negated_conjecture,(
% 2.20/0.66    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.20/0.66    inference(negated_conjecture,[],[f23])).
% 2.20/0.66  fof(f23,conjecture,(
% 2.20/0.66    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.20/0.66  fof(f79,plain,(
% 2.20/0.66    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.20/0.66    inference(definition_unfolding,[],[f46,f70])).
% 2.20/0.66  fof(f46,plain,(
% 2.20/0.66    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.20/0.66    inference(cnf_transformation,[],[f10])).
% 2.20/0.66  fof(f10,axiom,(
% 2.20/0.66    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.20/0.66  fof(f83,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 2.20/0.66    inference(definition_unfolding,[],[f56,f72,f72])).
% 2.20/0.66  fof(f56,plain,(
% 2.20/0.66    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.20/0.66    inference(cnf_transformation,[],[f21])).
% 2.20/0.66  fof(f21,axiom,(
% 2.20/0.66    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.20/0.66  fof(f287,plain,(
% 2.20/0.66    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 2.20/0.66    inference(superposition,[],[f89,f73])).
% 2.20/0.66  fof(f89,plain,(
% 2.20/0.66    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 2.20/0.66    inference(backward_demodulation,[],[f80,f60])).
% 2.20/0.66  fof(f80,plain,(
% 2.20/0.66    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 2.20/0.66    inference(definition_unfolding,[],[f47,f71])).
% 2.20/0.66  fof(f47,plain,(
% 2.20/0.66    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f6])).
% 2.20/0.66  fof(f6,axiom,(
% 2.20/0.66    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.20/0.66  fof(f350,plain,(
% 2.20/0.66    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0 | k1_xboole_0 = sK1) )),
% 2.20/0.66    inference(superposition,[],[f83,f341])).
% 2.20/0.66  fof(f356,plain,(
% 2.20/0.66    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 2.20/0.66    inference(trivial_inequality_removal,[],[f346])).
% 2.20/0.66  fof(f346,plain,(
% 2.20/0.66    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 2.20/0.66    inference(superposition,[],[f76,f341])).
% 2.20/0.66  fof(f76,plain,(
% 2.20/0.66    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 2.20/0.66    inference(definition_unfolding,[],[f34,f72])).
% 2.20/0.66  fof(f34,plain,(
% 2.20/0.66    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.20/0.66    inference(cnf_transformation,[],[f28])).
% 2.20/0.66  fof(f357,plain,(
% 2.20/0.66    sK1 != sK2 | k1_xboole_0 = sK1),
% 2.20/0.66    inference(trivial_inequality_removal,[],[f344])).
% 2.20/0.66  fof(f344,plain,(
% 2.20/0.66    sK1 != sK2 | sK1 != sK1 | k1_xboole_0 = sK1),
% 2.20/0.66    inference(superposition,[],[f74,f341])).
% 2.20/0.66  fof(f74,plain,(
% 2.20/0.66    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.20/0.66    inference(definition_unfolding,[],[f36,f72,f72])).
% 2.20/0.66  fof(f36,plain,(
% 2.20/0.66    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 2.20/0.66    inference(cnf_transformation,[],[f28])).
% 2.20/0.66  fof(f75,plain,(
% 2.20/0.66    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 2.20/0.66    inference(definition_unfolding,[],[f35,f72])).
% 2.20/0.66  fof(f35,plain,(
% 2.20/0.66    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 2.20/0.66    inference(cnf_transformation,[],[f28])).
% 2.20/0.66  fof(f307,plain,(
% 2.20/0.66    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.20/0.66    inference(unit_resulting_resolution,[],[f301,f266])).
% 2.20/0.66  fof(f266,plain,(
% 2.20/0.66    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 2.20/0.66    inference(duplicate_literal_removal,[],[f265])).
% 2.20/0.66  fof(f265,plain,(
% 2.20/0.66    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 2.20/0.66    inference(resolution,[],[f123,f54])).
% 2.20/0.66  fof(f54,plain,(
% 2.20/0.66    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f31])).
% 2.20/0.66  fof(f31,plain,(
% 2.20/0.66    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.20/0.66    inference(ennf_transformation,[],[f27])).
% 2.20/0.66  fof(f27,plain,(
% 2.20/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.20/0.66    inference(rectify,[],[f5])).
% 2.20/0.66  fof(f5,axiom,(
% 2.20/0.66    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.20/0.66  fof(f123,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1),X2) | ~r1_xboole_0(X2,X0) | r1_xboole_0(X0,X1)) )),
% 2.20/0.66    inference(resolution,[],[f52,f53])).
% 2.20/0.66  fof(f53,plain,(
% 2.20/0.66    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f31])).
% 2.20/0.66  fof(f52,plain,(
% 2.20/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 2.20/0.66    inference(cnf_transformation,[],[f31])).
% 2.20/0.66  fof(f301,plain,(
% 2.20/0.66    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 2.20/0.66    inference(unit_resulting_resolution,[],[f84,f267])).
% 2.20/0.66  fof(f267,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) )),
% 2.20/0.66    inference(duplicate_literal_removal,[],[f264])).
% 2.20/0.66  fof(f264,plain,(
% 2.20/0.66    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 2.20/0.66    inference(resolution,[],[f123,f53])).
% 2.20/0.66  fof(f84,plain,(
% 2.20/0.66    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.20/0.66    inference(equality_resolution,[],[f42])).
% 2.20/0.66  fof(f42,plain,(
% 2.20/0.66    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 2.20/0.66    inference(cnf_transformation,[],[f29])).
% 2.20/0.66  fof(f29,plain,(
% 2.20/0.66    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 2.20/0.66    inference(ennf_transformation,[],[f8])).
% 2.20/0.66  fof(f8,axiom,(
% 2.20/0.66    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 2.20/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 2.20/0.66  fof(f645,plain,(
% 2.20/0.66    r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 2.20/0.66    inference(forward_demodulation,[],[f635,f88])).
% 2.20/0.66  fof(f635,plain,(
% 2.20/0.66    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0)),
% 2.20/0.66    inference(backward_demodulation,[],[f287,f629])).
% 2.20/0.66  % SZS output end Proof for theBenchmark
% 2.20/0.66  % (18347)------------------------------
% 2.20/0.66  % (18347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.66  % (18347)Termination reason: Refutation
% 2.20/0.66  
% 2.20/0.66  % (18347)Memory used [KB]: 6908
% 2.20/0.66  % (18347)Time elapsed: 0.225 s
% 2.20/0.66  % (18347)------------------------------
% 2.20/0.66  % (18347)------------------------------
% 2.20/0.67  % (18321)Success in time 0.299 s
%------------------------------------------------------------------------------

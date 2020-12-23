%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:01 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  112 (1950 expanded)
%              Number of leaves         :   23 ( 640 expanded)
%              Depth                    :   23
%              Number of atoms          :  187 (2377 expanded)
%              Number of equality atoms :  126 (2247 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1386,plain,(
    $false ),
    inference(global_subsumption,[],[f1280,f1385])).

fof(f1385,plain,(
    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f1372,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f1372,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f126,f1311])).

fof(f1311,plain,(
    k1_xboole_0 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f761,f1282,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f1282,plain,(
    r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1241,f94])).

fof(f94,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f93,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f93,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f80,f79])).

fof(f79,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f47,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f61,f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f64,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f65,f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f80,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f42,f73])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f48,f72])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f1241,plain,(
    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) ),
    inference(backward_demodulation,[],[f438,f1234])).

fof(f1234,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f818,f817,f1227])).

fof(f1227,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f1224])).

fof(f1224,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f807,f820])).

fof(f820,plain,
    ( r1_tarski(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f819,f126])).

fof(f819,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f803,f120])).

fof(f120,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f62,f45])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f62,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f803,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f438,f796])).

fof(f796,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f89,f386])).

fof(f386,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f81,f75])).

fof(f75,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f35,f74,f72])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f71])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f72])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f56,f74,f74])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f807,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK1 = X0
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f89,f796])).

fof(f817,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f800])).

fof(f800,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f78,f796])).

fof(f78,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f32,f74])).

fof(f32,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f29])).

fof(f818,plain,
    ( sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f798])).

fof(f798,plain,
    ( sK1 != sK2
    | sK1 != sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f76,f796])).

fof(f76,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f34,f74,f74])).

fof(f34,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f438,plain,(
    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(superposition,[],[f99,f75])).

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(backward_demodulation,[],[f82,f62])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f44,f73])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f761,plain,(
    ! [X0] : ~ r2_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f754,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,X1) )
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ~ r2_hidden(X2,X0)
              & r2_hidden(X2,X1) )
        & r2_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).

fof(f754,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f753,f79])).

fof(f753,plain,(
    ! [X0] : ~ r2_hidden(X0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(forward_demodulation,[],[f736,f126])).

fof(f736,plain,(
    ! [X0] : ~ r2_hidden(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))))) ),
    inference(unit_resulting_resolution,[],[f654,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(backward_demodulation,[],[f84,f62])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f73])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f654,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f652,f79])).

fof(f652,plain,(
    r1_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f79,f640])).

fof(f640,plain,(
    ! [X0] :
      ( k1_xboole_0 != X0
      | r1_xboole_0(X0,X0) ) ),
    inference(forward_demodulation,[],[f629,f126])).

fof(f629,plain,(
    ! [X0] :
      ( k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X0,X0))
      | r1_xboole_0(X0,X0) ) ),
    inference(superposition,[],[f95,f79])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))
      | r1_xboole_0(X0,X1) ) ),
    inference(backward_demodulation,[],[f86,f62])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f73])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f126,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f112,f94])).

fof(f112,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f62,f36])).

fof(f1280,plain,(
    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(global_subsumption,[],[f77,f1234])).

fof(f77,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f33,f74])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:23:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (2628)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (2627)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (2624)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (2625)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (2626)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (2630)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (2645)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.54  % (2638)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.54  % (2647)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (2637)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.54  % (2649)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (2650)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.54  % (2623)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (2638)Refutation not found, incomplete strategy% (2638)------------------------------
% 0.22/0.54  % (2638)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (2638)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (2638)Memory used [KB]: 6140
% 0.22/0.54  % (2638)Time elapsed: 0.101 s
% 0.22/0.54  % (2638)------------------------------
% 0.22/0.54  % (2638)------------------------------
% 0.22/0.55  % (2652)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (2651)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (2648)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.55  % (2644)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.55  % (2643)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.55  % (2629)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.55  % (2644)Refutation not found, incomplete strategy% (2644)------------------------------
% 0.22/0.55  % (2644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (2644)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (2644)Memory used [KB]: 1791
% 0.22/0.55  % (2644)Time elapsed: 0.149 s
% 0.22/0.55  % (2644)------------------------------
% 0.22/0.55  % (2644)------------------------------
% 0.22/0.55  % (2639)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (2641)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.55  % (2642)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.55  % (2636)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.56  % (2640)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.56  % (2640)Refutation not found, incomplete strategy% (2640)------------------------------
% 0.22/0.56  % (2640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (2640)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (2640)Memory used [KB]: 10618
% 0.22/0.56  % (2640)Time elapsed: 0.147 s
% 0.22/0.56  % (2640)------------------------------
% 0.22/0.56  % (2640)------------------------------
% 0.22/0.56  % (2635)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.56  % (2631)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.56  % (2633)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.56  % (2634)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (2632)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.56  % (2633)Refutation not found, incomplete strategy% (2633)------------------------------
% 0.22/0.56  % (2633)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (2633)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (2633)Memory used [KB]: 10618
% 0.22/0.56  % (2633)Time elapsed: 0.150 s
% 0.22/0.56  % (2633)------------------------------
% 0.22/0.56  % (2633)------------------------------
% 0.22/0.56  % (2645)Refutation not found, incomplete strategy% (2645)------------------------------
% 0.22/0.56  % (2645)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (2645)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (2645)Memory used [KB]: 10874
% 0.22/0.56  % (2645)Time elapsed: 0.099 s
% 0.22/0.56  % (2645)------------------------------
% 0.22/0.56  % (2645)------------------------------
% 0.22/0.56  % (2631)Refutation not found, incomplete strategy% (2631)------------------------------
% 0.22/0.56  % (2631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (2631)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (2631)Memory used [KB]: 10746
% 0.22/0.56  % (2631)Time elapsed: 0.151 s
% 0.22/0.56  % (2631)------------------------------
% 0.22/0.56  % (2631)------------------------------
% 0.22/0.57  % (2646)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.59  % (2649)Refutation not found, incomplete strategy% (2649)------------------------------
% 0.22/0.59  % (2649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (2649)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (2649)Memory used [KB]: 10874
% 0.22/0.59  % (2649)Time elapsed: 0.179 s
% 0.22/0.59  % (2649)------------------------------
% 0.22/0.59  % (2649)------------------------------
% 2.18/0.67  % (2647)Refutation found. Thanks to Tanya!
% 2.18/0.67  % SZS status Theorem for theBenchmark
% 2.18/0.67  % SZS output start Proof for theBenchmark
% 2.18/0.67  fof(f1386,plain,(
% 2.18/0.67    $false),
% 2.18/0.67    inference(global_subsumption,[],[f1280,f1385])).
% 2.18/0.67  fof(f1385,plain,(
% 2.18/0.67    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.18/0.67    inference(forward_demodulation,[],[f1372,f37])).
% 2.18/0.67  fof(f37,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.18/0.67    inference(cnf_transformation,[],[f10])).
% 2.18/0.67  fof(f10,axiom,(
% 2.18/0.67    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.18/0.67  fof(f1372,plain,(
% 2.18/0.67    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k1_xboole_0)),
% 2.18/0.67    inference(superposition,[],[f126,f1311])).
% 2.18/0.67  fof(f1311,plain,(
% 2.18/0.67    k1_xboole_0 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.18/0.67    inference(unit_resulting_resolution,[],[f761,f1282,f53])).
% 2.18/0.67  fof(f53,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f4])).
% 2.18/0.67  fof(f4,axiom,(
% 2.18/0.67    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 2.18/0.67  fof(f1282,plain,(
% 2.18/0.67    r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 2.18/0.67    inference(forward_demodulation,[],[f1241,f94])).
% 2.18/0.67  fof(f94,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.18/0.67    inference(forward_demodulation,[],[f93,f36])).
% 2.18/0.67  fof(f36,plain,(
% 2.18/0.67    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f13])).
% 2.18/0.67  fof(f13,axiom,(
% 2.18/0.67    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.18/0.67  fof(f93,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 2.18/0.67    inference(forward_demodulation,[],[f80,f79])).
% 2.18/0.67  fof(f79,plain,(
% 2.18/0.67    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.18/0.67    inference(definition_unfolding,[],[f41,f72])).
% 2.18/0.67  fof(f72,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.18/0.67    inference(definition_unfolding,[],[f46,f71])).
% 2.18/0.67  fof(f71,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f47,f70])).
% 2.18/0.67  fof(f70,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f61,f69])).
% 2.18/0.67  fof(f69,plain,(
% 2.18/0.67    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f63,f68])).
% 2.18/0.67  fof(f68,plain,(
% 2.18/0.67    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f64,f67])).
% 2.18/0.67  fof(f67,plain,(
% 2.18/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f65,f66])).
% 2.18/0.67  fof(f66,plain,(
% 2.18/0.67    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f21])).
% 2.18/0.67  fof(f21,axiom,(
% 2.18/0.67    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.18/0.67  fof(f65,plain,(
% 2.18/0.67    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f20])).
% 2.18/0.67  fof(f20,axiom,(
% 2.18/0.67    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.18/0.67  fof(f64,plain,(
% 2.18/0.67    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f19])).
% 2.18/0.67  fof(f19,axiom,(
% 2.18/0.67    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.18/0.67  fof(f63,plain,(
% 2.18/0.67    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f18])).
% 2.18/0.67  fof(f18,axiom,(
% 2.18/0.67    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.18/0.67  fof(f61,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f17])).
% 2.18/0.67  fof(f17,axiom,(
% 2.18/0.67    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.18/0.67  fof(f47,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f16])).
% 2.18/0.67  fof(f16,axiom,(
% 2.18/0.67    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.18/0.67  fof(f46,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f23])).
% 2.18/0.67  fof(f23,axiom,(
% 2.18/0.67    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.18/0.67  fof(f41,plain,(
% 2.18/0.67    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.18/0.67    inference(cnf_transformation,[],[f26])).
% 2.18/0.67  fof(f26,plain,(
% 2.18/0.67    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.18/0.67    inference(rectify,[],[f5])).
% 2.18/0.67  fof(f5,axiom,(
% 2.18/0.67    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.18/0.67  fof(f80,plain,(
% 2.18/0.67    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 2.18/0.67    inference(definition_unfolding,[],[f42,f73])).
% 2.18/0.67  fof(f73,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.18/0.67    inference(definition_unfolding,[],[f48,f72])).
% 2.18/0.67  fof(f48,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f14])).
% 2.18/0.67  fof(f14,axiom,(
% 2.18/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.18/0.67  fof(f42,plain,(
% 2.18/0.67    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.18/0.67    inference(cnf_transformation,[],[f27])).
% 2.18/0.67  fof(f27,plain,(
% 2.18/0.67    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.18/0.67    inference(rectify,[],[f6])).
% 2.18/0.67  fof(f6,axiom,(
% 2.18/0.67    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.18/0.67  fof(f1241,plain,(
% 2.18/0.67    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0)),
% 2.18/0.67    inference(backward_demodulation,[],[f438,f1234])).
% 2.18/0.67  fof(f1234,plain,(
% 2.18/0.67    k1_xboole_0 = sK1),
% 2.18/0.67    inference(global_subsumption,[],[f818,f817,f1227])).
% 2.18/0.67  fof(f1227,plain,(
% 2.18/0.67    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 2.18/0.67    inference(duplicate_literal_removal,[],[f1224])).
% 2.18/0.67  fof(f1224,plain,(
% 2.18/0.67    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 2.18/0.67    inference(resolution,[],[f807,f820])).
% 2.18/0.67  fof(f820,plain,(
% 2.18/0.67    r1_tarski(sK2,sK1) | k1_xboole_0 = sK1),
% 2.18/0.67    inference(forward_demodulation,[],[f819,f126])).
% 2.18/0.67  fof(f819,plain,(
% 2.18/0.67    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1) | k1_xboole_0 = sK1),
% 2.18/0.67    inference(forward_demodulation,[],[f803,f120])).
% 2.18/0.67  fof(f120,plain,(
% 2.18/0.67    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 2.18/0.67    inference(superposition,[],[f62,f45])).
% 2.18/0.67  fof(f45,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f1])).
% 2.18/0.67  fof(f1,axiom,(
% 2.18/0.67    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.18/0.67  fof(f62,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f12])).
% 2.18/0.67  fof(f12,axiom,(
% 2.18/0.67    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.18/0.67  fof(f803,plain,(
% 2.18/0.67    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) | k1_xboole_0 = sK1),
% 2.18/0.67    inference(superposition,[],[f438,f796])).
% 2.18/0.67  fof(f796,plain,(
% 2.18/0.67    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1),
% 2.18/0.67    inference(resolution,[],[f89,f386])).
% 2.18/0.67  fof(f386,plain,(
% 2.18/0.67    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.18/0.67    inference(superposition,[],[f81,f75])).
% 2.18/0.67  fof(f75,plain,(
% 2.18/0.67    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.18/0.67    inference(definition_unfolding,[],[f35,f74,f72])).
% 2.18/0.67  fof(f74,plain,(
% 2.18/0.67    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f38,f71])).
% 2.18/0.67  fof(f38,plain,(
% 2.18/0.67    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f15])).
% 2.18/0.67  fof(f15,axiom,(
% 2.18/0.67    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.18/0.67  fof(f35,plain,(
% 2.18/0.67    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.18/0.67    inference(cnf_transformation,[],[f29])).
% 2.18/0.67  fof(f29,plain,(
% 2.18/0.67    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.18/0.67    inference(ennf_transformation,[],[f25])).
% 2.18/0.67  fof(f25,negated_conjecture,(
% 2.18/0.67    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.18/0.67    inference(negated_conjecture,[],[f24])).
% 2.18/0.67  fof(f24,conjecture,(
% 2.18/0.67    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.18/0.67  fof(f81,plain,(
% 2.18/0.67    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.18/0.67    inference(definition_unfolding,[],[f43,f72])).
% 2.18/0.67  fof(f43,plain,(
% 2.18/0.67    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f11])).
% 2.18/0.67  fof(f11,axiom,(
% 2.18/0.67    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.18/0.67  fof(f89,plain,(
% 2.18/0.67    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 2.18/0.67    inference(definition_unfolding,[],[f56,f74,f74])).
% 2.18/0.67  fof(f56,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.18/0.67    inference(cnf_transformation,[],[f22])).
% 2.18/0.67  fof(f22,axiom,(
% 2.18/0.67    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.18/0.67  fof(f807,plain,(
% 2.18/0.67    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0 | k1_xboole_0 = sK1) )),
% 2.18/0.67    inference(superposition,[],[f89,f796])).
% 2.18/0.67  fof(f817,plain,(
% 2.18/0.67    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 2.18/0.67    inference(trivial_inequality_removal,[],[f800])).
% 2.18/0.67  fof(f800,plain,(
% 2.18/0.67    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 2.18/0.67    inference(superposition,[],[f78,f796])).
% 2.18/0.67  fof(f78,plain,(
% 2.18/0.67    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 2.18/0.67    inference(definition_unfolding,[],[f32,f74])).
% 2.18/0.67  fof(f32,plain,(
% 2.18/0.67    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.18/0.67    inference(cnf_transformation,[],[f29])).
% 2.18/0.67  fof(f818,plain,(
% 2.18/0.67    sK1 != sK2 | k1_xboole_0 = sK1),
% 2.18/0.67    inference(trivial_inequality_removal,[],[f798])).
% 2.18/0.67  fof(f798,plain,(
% 2.18/0.67    sK1 != sK2 | sK1 != sK1 | k1_xboole_0 = sK1),
% 2.18/0.67    inference(superposition,[],[f76,f796])).
% 2.18/0.67  fof(f76,plain,(
% 2.18/0.67    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.18/0.67    inference(definition_unfolding,[],[f34,f74,f74])).
% 2.18/0.67  fof(f34,plain,(
% 2.18/0.67    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 2.18/0.67    inference(cnf_transformation,[],[f29])).
% 2.18/0.67  fof(f438,plain,(
% 2.18/0.67    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 2.18/0.67    inference(superposition,[],[f99,f75])).
% 2.18/0.67  fof(f99,plain,(
% 2.18/0.67    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 2.18/0.67    inference(backward_demodulation,[],[f82,f62])).
% 2.18/0.67  fof(f82,plain,(
% 2.18/0.67    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f44,f73])).
% 2.18/0.67  fof(f44,plain,(
% 2.18/0.67    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f9])).
% 2.18/0.67  fof(f9,axiom,(
% 2.18/0.67    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.18/0.67  fof(f761,plain,(
% 2.18/0.67    ( ! [X0] : (~r2_xboole_0(X0,k1_xboole_0)) )),
% 2.18/0.67    inference(unit_resulting_resolution,[],[f754,f59])).
% 2.18/0.67  fof(f59,plain,(
% 2.18/0.67    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | ~r2_xboole_0(X0,X1)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f31])).
% 2.18/0.67  fof(f31,plain,(
% 2.18/0.67    ! [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | ~r2_xboole_0(X0,X1))),
% 2.18/0.67    inference(ennf_transformation,[],[f8])).
% 2.18/0.67  fof(f8,axiom,(
% 2.18/0.67    ! [X0,X1] : ~(! [X2] : ~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & r2_xboole_0(X0,X1))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_0)).
% 2.18/0.67  fof(f754,plain,(
% 2.18/0.67    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.18/0.67    inference(forward_demodulation,[],[f753,f79])).
% 2.18/0.67  fof(f753,plain,(
% 2.18/0.67    ( ! [X0] : (~r2_hidden(X0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))) )),
% 2.18/0.67    inference(forward_demodulation,[],[f736,f126])).
% 2.18/0.67  fof(f736,plain,(
% 2.18/0.67    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))))) )),
% 2.18/0.67    inference(unit_resulting_resolution,[],[f654,f97])).
% 2.18/0.67  fof(f97,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) | ~r1_xboole_0(X0,X1)) )),
% 2.18/0.67    inference(backward_demodulation,[],[f84,f62])).
% 2.18/0.67  fof(f84,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X2,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | ~r1_xboole_0(X0,X1)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f49,f73])).
% 2.18/0.67  fof(f49,plain,(
% 2.18/0.67    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f30])).
% 2.18/0.67  fof(f30,plain,(
% 2.18/0.67    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.18/0.67    inference(ennf_transformation,[],[f28])).
% 2.18/0.67  fof(f28,plain,(
% 2.18/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.18/0.67    inference(rectify,[],[f7])).
% 2.18/0.67  fof(f7,axiom,(
% 2.18/0.67    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.18/0.67  fof(f654,plain,(
% 2.18/0.67    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 2.18/0.67    inference(forward_demodulation,[],[f652,f79])).
% 2.18/0.67  fof(f652,plain,(
% 2.18/0.67    r1_xboole_0(k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0)))),
% 2.18/0.67    inference(unit_resulting_resolution,[],[f79,f640])).
% 2.18/0.67  fof(f640,plain,(
% 2.18/0.67    ( ! [X0] : (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)) )),
% 2.18/0.67    inference(forward_demodulation,[],[f629,f126])).
% 2.18/0.67  fof(f629,plain,(
% 2.18/0.67    ( ! [X0] : (k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X0,X0)) | r1_xboole_0(X0,X0)) )),
% 2.18/0.67    inference(superposition,[],[f95,f79])).
% 2.18/0.67  fof(f95,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) | r1_xboole_0(X0,X1)) )),
% 2.18/0.67    inference(backward_demodulation,[],[f86,f62])).
% 2.18/0.67  fof(f86,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) | r1_xboole_0(X0,X1)) )),
% 2.18/0.67    inference(definition_unfolding,[],[f54,f73])).
% 2.18/0.67  fof(f54,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 2.18/0.67    inference(cnf_transformation,[],[f3])).
% 2.18/0.67  fof(f3,axiom,(
% 2.18/0.67    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.18/0.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.18/0.67  fof(f126,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.18/0.67    inference(forward_demodulation,[],[f112,f94])).
% 2.18/0.67  fof(f112,plain,(
% 2.18/0.67    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.18/0.67    inference(superposition,[],[f62,f36])).
% 2.18/0.67  fof(f1280,plain,(
% 2.18/0.67    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.18/0.67    inference(global_subsumption,[],[f77,f1234])).
% 2.18/0.67  fof(f77,plain,(
% 2.18/0.67    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 2.18/0.67    inference(definition_unfolding,[],[f33,f74])).
% 2.18/0.67  fof(f33,plain,(
% 2.18/0.67    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 2.18/0.67    inference(cnf_transformation,[],[f29])).
% 2.18/0.67  % SZS output end Proof for theBenchmark
% 2.18/0.67  % (2647)------------------------------
% 2.18/0.67  % (2647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.67  % (2647)Termination reason: Refutation
% 2.18/0.67  
% 2.18/0.67  % (2647)Memory used [KB]: 7547
% 2.18/0.67  % (2647)Time elapsed: 0.245 s
% 2.18/0.67  % (2647)------------------------------
% 2.18/0.67  % (2647)------------------------------
% 2.18/0.67  % (2622)Success in time 0.299 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:00 EST 2020

% Result     : Theorem 1.29s
% Output     : Refutation 1.29s
% Verified   : 
% Statistics : Number of formulae       :  105 (1675 expanded)
%              Number of leaves         :   23 ( 550 expanded)
%              Depth                    :   23
%              Number of atoms          :  187 (2109 expanded)
%              Number of equality atoms :  125 (1978 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f597,plain,(
    $false ),
    inference(global_subsumption,[],[f551,f596])).

fof(f596,plain,(
    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f588,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f588,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f150,f566])).

fof(f566,plain,(
    k1_xboole_0 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f110,f553,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f553,plain,(
    r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f548,f92])).

fof(f92,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f91,f80])).

fof(f80,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f42,f72])).

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
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f47,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f91,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(forward_demodulation,[],[f79,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f41,f73])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f48,f72])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f41,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f548,plain,(
    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0) ),
    inference(backward_demodulation,[],[f267,f541])).

fof(f541,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f365,f364,f540])).

fof(f540,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1 ),
    inference(duplicate_literal_removal,[],[f533])).

fof(f533,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f359,f367])).

fof(f367,plain,
    ( r1_tarski(sK2,sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f366,f150])).

fof(f366,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1)
    | k1_xboole_0 = sK1 ),
    inference(forward_demodulation,[],[f354,f144])).

fof(f144,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f62,f45])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f62,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f354,plain,
    ( r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f267,f350])).

fof(f350,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f85,f241])).

fof(f241,plain,(
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
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f43,f72])).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f58,f74,f74])).

fof(f58,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f359,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK1 = X0
      | k1_xboole_0 = X0
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f85,f350])).

fof(f364,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f357])).

fof(f357,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f78,f350])).

fof(f78,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f32,f74])).

fof(f32,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f365,plain,
    ( sK1 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f356])).

fof(f356,plain,
    ( sK1 != sK2
    | sK1 != sK1
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f76,f350])).

fof(f76,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f34,f74,f74])).

fof(f34,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f267,plain,(
    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(superposition,[],[f93,f75])).

fof(f93,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(backward_demodulation,[],[f82,f62])).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f44,f73])).

fof(f44,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f110,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f107,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f107,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f49,f86])).

fof(f86,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f150,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f136,f92])).

fof(f136,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f62,f36])).

fof(f551,plain,(
    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(global_subsumption,[],[f77,f541])).

fof(f77,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f33,f74])).

fof(f33,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:24:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.36  ipcrm: permission denied for id (807108609)
% 0.20/0.36  ipcrm: permission denied for id (806453252)
% 0.20/0.36  ipcrm: permission denied for id (807206917)
% 0.20/0.36  ipcrm: permission denied for id (807272455)
% 0.20/0.36  ipcrm: permission denied for id (807337993)
% 0.20/0.37  ipcrm: permission denied for id (807370762)
% 0.20/0.37  ipcrm: permission denied for id (807436300)
% 0.20/0.37  ipcrm: permission denied for id (807469069)
% 0.20/0.37  ipcrm: permission denied for id (807600145)
% 0.20/0.38  ipcrm: permission denied for id (807698452)
% 0.20/0.38  ipcrm: permission denied for id (807763990)
% 0.20/0.38  ipcrm: permission denied for id (806518808)
% 0.20/0.38  ipcrm: permission denied for id (807829529)
% 0.20/0.38  ipcrm: permission denied for id (807862298)
% 0.20/0.39  ipcrm: permission denied for id (806551579)
% 0.20/0.39  ipcrm: permission denied for id (806584348)
% 0.20/0.39  ipcrm: permission denied for id (807895069)
% 0.20/0.39  ipcrm: permission denied for id (807927838)
% 0.20/0.39  ipcrm: permission denied for id (807993376)
% 0.20/0.39  ipcrm: permission denied for id (806617122)
% 0.20/0.39  ipcrm: permission denied for id (808058915)
% 0.20/0.40  ipcrm: permission denied for id (808091684)
% 0.20/0.40  ipcrm: permission denied for id (808222759)
% 0.20/0.41  ipcrm: permission denied for id (808386604)
% 0.20/0.41  ipcrm: permission denied for id (808419373)
% 0.20/0.41  ipcrm: permission denied for id (808452142)
% 0.20/0.41  ipcrm: permission denied for id (808484911)
% 0.20/0.41  ipcrm: permission denied for id (806649905)
% 0.20/0.41  ipcrm: permission denied for id (808583219)
% 0.20/0.42  ipcrm: permission denied for id (808812602)
% 0.20/0.42  ipcrm: permission denied for id (808845371)
% 0.20/0.42  ipcrm: permission denied for id (808878140)
% 0.20/0.42  ipcrm: permission denied for id (808910909)
% 0.20/0.43  ipcrm: permission denied for id (808943678)
% 0.20/0.43  ipcrm: permission denied for id (808976447)
% 0.20/0.43  ipcrm: permission denied for id (809009216)
% 0.20/0.43  ipcrm: permission denied for id (809041985)
% 0.20/0.43  ipcrm: permission denied for id (809173060)
% 0.20/0.44  ipcrm: permission denied for id (809336905)
% 0.20/0.44  ipcrm: permission denied for id (806715466)
% 0.20/0.44  ipcrm: permission denied for id (809369675)
% 0.20/0.44  ipcrm: permission denied for id (809435213)
% 0.20/0.44  ipcrm: permission denied for id (809467982)
% 0.20/0.45  ipcrm: permission denied for id (809500751)
% 0.20/0.45  ipcrm: permission denied for id (806813776)
% 0.20/0.45  ipcrm: permission denied for id (806846546)
% 0.20/0.45  ipcrm: permission denied for id (806879316)
% 0.20/0.45  ipcrm: permission denied for id (809631830)
% 0.20/0.46  ipcrm: permission denied for id (809697368)
% 0.20/0.46  ipcrm: permission denied for id (806912089)
% 0.20/0.46  ipcrm: permission denied for id (809730138)
% 0.20/0.46  ipcrm: permission denied for id (809762907)
% 0.20/0.46  ipcrm: permission denied for id (809893983)
% 0.20/0.47  ipcrm: permission denied for id (809959521)
% 0.20/0.47  ipcrm: permission denied for id (809992290)
% 0.20/0.47  ipcrm: permission denied for id (810025059)
% 0.20/0.47  ipcrm: permission denied for id (810057828)
% 0.20/0.47  ipcrm: permission denied for id (810090597)
% 0.20/0.47  ipcrm: permission denied for id (810123366)
% 0.20/0.47  ipcrm: permission denied for id (810188904)
% 0.20/0.48  ipcrm: permission denied for id (810254442)
% 0.20/0.48  ipcrm: permission denied for id (810352749)
% 0.20/0.48  ipcrm: permission denied for id (810385518)
% 0.20/0.48  ipcrm: permission denied for id (810418287)
% 0.20/0.48  ipcrm: permission denied for id (807043184)
% 0.20/0.49  ipcrm: permission denied for id (810483826)
% 0.20/0.49  ipcrm: permission denied for id (810516595)
% 0.20/0.49  ipcrm: permission denied for id (810647671)
% 0.20/0.49  ipcrm: permission denied for id (810713209)
% 0.20/0.50  ipcrm: permission denied for id (810778747)
% 0.83/0.63  % (18453)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.83/0.64  % (18469)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.83/0.64  % (18461)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.65  % (18456)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.29/0.65  % (18473)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.29/0.66  % (18452)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.29/0.66  % (18477)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.29/0.66  % (18471)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.29/0.66  % (18463)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.29/0.66  % (18464)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.29/0.67  % (18455)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.29/0.67  % (18471)Refutation not found, incomplete strategy% (18471)------------------------------
% 1.29/0.67  % (18471)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.67  % (18471)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.67  
% 1.29/0.67  % (18471)Memory used [KB]: 10746
% 1.29/0.67  % (18471)Time elapsed: 0.063 s
% 1.29/0.67  % (18471)------------------------------
% 1.29/0.67  % (18471)------------------------------
% 1.29/0.68  % (18451)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.29/0.68  % (18466)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.29/0.68  % (18462)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.29/0.68  % (18475)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.29/0.68  % (18472)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.29/0.69  % (18451)Refutation not found, incomplete strategy% (18451)------------------------------
% 1.29/0.69  % (18451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.69  % (18476)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.29/0.69  % (18450)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.29/0.69  % (18468)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.29/0.69  % (18467)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.29/0.69  % (18460)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.29/0.69  % (18460)Refutation not found, incomplete strategy% (18460)------------------------------
% 1.29/0.69  % (18460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.69  % (18459)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.29/0.69  % (18451)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.69  
% 1.29/0.69  % (18451)Memory used [KB]: 10746
% 1.29/0.69  % (18451)Time elapsed: 0.132 s
% 1.29/0.69  % (18451)------------------------------
% 1.29/0.69  % (18451)------------------------------
% 1.29/0.69  % (18458)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.29/0.69  % (18474)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.29/0.69  % (18459)Refutation not found, incomplete strategy% (18459)------------------------------
% 1.29/0.69  % (18459)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.70  % (18478)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.29/0.70  % (18454)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.29/0.70  % (18465)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.29/0.70  % (18449)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.29/0.70  % (18470)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.29/0.71  % (18460)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.71  
% 1.29/0.71  % (18460)Memory used [KB]: 10618
% 1.29/0.71  % (18460)Time elapsed: 0.138 s
% 1.29/0.71  % (18460)------------------------------
% 1.29/0.71  % (18460)------------------------------
% 1.29/0.71  % (18459)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.71  
% 1.29/0.71  % (18459)Memory used [KB]: 10618
% 1.29/0.71  % (18459)Time elapsed: 0.147 s
% 1.29/0.71  % (18459)------------------------------
% 1.29/0.71  % (18459)------------------------------
% 1.29/0.71  % (18457)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.29/0.71  % (18470)Refutation not found, incomplete strategy% (18470)------------------------------
% 1.29/0.71  % (18470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.71  % (18473)Refutation found. Thanks to Tanya!
% 1.29/0.71  % SZS status Theorem for theBenchmark
% 1.29/0.71  % (18466)Refutation not found, incomplete strategy% (18466)------------------------------
% 1.29/0.71  % (18466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.71  % (18466)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.71  
% 1.29/0.71  % (18466)Memory used [KB]: 10618
% 1.29/0.71  % (18466)Time elapsed: 0.161 s
% 1.29/0.71  % (18466)------------------------------
% 1.29/0.71  % (18466)------------------------------
% 1.29/0.72  % (18470)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.72  
% 1.29/0.72  % (18470)Memory used [KB]: 1791
% 1.29/0.72  % (18470)Time elapsed: 0.158 s
% 1.29/0.72  % (18470)------------------------------
% 1.29/0.72  % (18470)------------------------------
% 1.29/0.72  % (18457)Refutation not found, incomplete strategy% (18457)------------------------------
% 1.29/0.72  % (18457)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.72  % (18457)Termination reason: Refutation not found, incomplete strategy
% 1.29/0.72  
% 1.29/0.72  % (18457)Memory used [KB]: 10746
% 1.29/0.72  % (18457)Time elapsed: 0.174 s
% 1.29/0.72  % (18457)------------------------------
% 1.29/0.72  % (18457)------------------------------
% 1.29/0.73  % SZS output start Proof for theBenchmark
% 1.29/0.73  fof(f597,plain,(
% 1.29/0.73    $false),
% 1.29/0.73    inference(global_subsumption,[],[f551,f596])).
% 1.29/0.73  fof(f596,plain,(
% 1.29/0.73    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.29/0.73    inference(forward_demodulation,[],[f588,f37])).
% 1.29/0.73  fof(f37,plain,(
% 1.29/0.73    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.29/0.73    inference(cnf_transformation,[],[f8])).
% 1.29/0.73  fof(f8,axiom,(
% 1.29/0.73    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.29/0.73  fof(f588,plain,(
% 1.29/0.73    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k1_xboole_0)),
% 1.29/0.73    inference(superposition,[],[f150,f566])).
% 1.29/0.73  fof(f566,plain,(
% 1.29/0.73    k1_xboole_0 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.29/0.73    inference(unit_resulting_resolution,[],[f110,f553,f54])).
% 1.29/0.73  fof(f54,plain,(
% 1.29/0.73    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.29/0.73    inference(cnf_transformation,[],[f6])).
% 1.29/0.73  fof(f6,axiom,(
% 1.29/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.29/0.73  fof(f553,plain,(
% 1.29/0.73    r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k1_xboole_0)),
% 1.29/0.73    inference(forward_demodulation,[],[f548,f92])).
% 1.29/0.73  fof(f92,plain,(
% 1.29/0.73    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.29/0.73    inference(backward_demodulation,[],[f91,f80])).
% 1.29/0.73  fof(f80,plain,(
% 1.29/0.73    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.29/0.73    inference(definition_unfolding,[],[f42,f72])).
% 1.29/0.73  fof(f72,plain,(
% 1.29/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.29/0.73    inference(definition_unfolding,[],[f46,f71])).
% 1.29/0.73  fof(f71,plain,(
% 1.29/0.73    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.29/0.73    inference(definition_unfolding,[],[f47,f70])).
% 1.29/0.73  fof(f70,plain,(
% 1.29/0.73    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.29/0.73    inference(definition_unfolding,[],[f61,f69])).
% 1.29/0.73  fof(f69,plain,(
% 1.29/0.73    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.29/0.73    inference(definition_unfolding,[],[f63,f68])).
% 1.29/0.73  fof(f68,plain,(
% 1.29/0.73    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.29/0.73    inference(definition_unfolding,[],[f64,f67])).
% 1.29/0.73  fof(f67,plain,(
% 1.29/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.29/0.73    inference(definition_unfolding,[],[f65,f66])).
% 1.29/0.73  fof(f66,plain,(
% 1.29/0.73    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.29/0.73    inference(cnf_transformation,[],[f20])).
% 1.29/0.73  fof(f20,axiom,(
% 1.29/0.73    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.29/0.73  fof(f65,plain,(
% 1.29/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.29/0.73    inference(cnf_transformation,[],[f19])).
% 1.29/0.73  fof(f19,axiom,(
% 1.29/0.73    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.29/0.73  fof(f64,plain,(
% 1.29/0.73    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.29/0.73    inference(cnf_transformation,[],[f18])).
% 1.29/0.73  fof(f18,axiom,(
% 1.29/0.73    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.29/0.73  fof(f63,plain,(
% 1.29/0.73    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.29/0.73    inference(cnf_transformation,[],[f17])).
% 1.29/0.73  fof(f17,axiom,(
% 1.29/0.73    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.29/0.73  fof(f61,plain,(
% 1.29/0.73    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.29/0.73    inference(cnf_transformation,[],[f16])).
% 1.29/0.73  fof(f16,axiom,(
% 1.29/0.73    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.29/0.73  fof(f47,plain,(
% 1.29/0.73    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.29/0.73    inference(cnf_transformation,[],[f15])).
% 1.29/0.73  fof(f15,axiom,(
% 1.29/0.73    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.29/0.73  fof(f46,plain,(
% 1.29/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.29/0.73    inference(cnf_transformation,[],[f22])).
% 1.29/0.73  fof(f22,axiom,(
% 1.29/0.73    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.29/0.73  fof(f42,plain,(
% 1.29/0.73    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.29/0.73    inference(cnf_transformation,[],[f26])).
% 1.29/0.73  fof(f26,plain,(
% 1.29/0.73    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.29/0.73    inference(rectify,[],[f3])).
% 1.29/0.73  fof(f3,axiom,(
% 1.29/0.73    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.29/0.73  fof(f91,plain,(
% 1.29/0.73    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 1.29/0.73    inference(forward_demodulation,[],[f79,f36])).
% 1.29/0.73  fof(f36,plain,(
% 1.29/0.73    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.29/0.73    inference(cnf_transformation,[],[f12])).
% 1.29/0.73  fof(f12,axiom,(
% 1.29/0.73    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.29/0.73  fof(f79,plain,(
% 1.29/0.73    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 1.29/0.73    inference(definition_unfolding,[],[f41,f73])).
% 1.29/0.73  fof(f73,plain,(
% 1.29/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.29/0.73    inference(definition_unfolding,[],[f48,f72])).
% 1.29/0.73  fof(f48,plain,(
% 1.29/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.29/0.73    inference(cnf_transformation,[],[f13])).
% 1.29/0.73  fof(f13,axiom,(
% 1.29/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.29/0.73  fof(f41,plain,(
% 1.29/0.73    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.29/0.73    inference(cnf_transformation,[],[f25])).
% 1.29/0.73  fof(f25,plain,(
% 1.29/0.73    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.29/0.73    inference(rectify,[],[f4])).
% 1.29/0.73  fof(f4,axiom,(
% 1.29/0.73    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.29/0.73  fof(f548,plain,(
% 1.29/0.73    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k1_xboole_0)),
% 1.29/0.73    inference(backward_demodulation,[],[f267,f541])).
% 1.29/0.73  fof(f541,plain,(
% 1.29/0.73    k1_xboole_0 = sK1),
% 1.29/0.73    inference(global_subsumption,[],[f365,f364,f540])).
% 1.29/0.73  fof(f540,plain,(
% 1.29/0.73    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1),
% 1.29/0.73    inference(duplicate_literal_removal,[],[f533])).
% 1.29/0.73  fof(f533,plain,(
% 1.29/0.73    sK1 = sK2 | k1_xboole_0 = sK2 | k1_xboole_0 = sK1 | k1_xboole_0 = sK1),
% 1.29/0.73    inference(resolution,[],[f359,f367])).
% 1.29/0.73  fof(f367,plain,(
% 1.29/0.73    r1_tarski(sK2,sK1) | k1_xboole_0 = sK1),
% 1.29/0.73    inference(forward_demodulation,[],[f366,f150])).
% 1.29/0.73  fof(f366,plain,(
% 1.29/0.73    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)),sK1) | k1_xboole_0 = sK1),
% 1.29/0.73    inference(forward_demodulation,[],[f354,f144])).
% 1.29/0.73  fof(f144,plain,(
% 1.29/0.73    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 1.29/0.73    inference(superposition,[],[f62,f45])).
% 1.29/0.73  fof(f45,plain,(
% 1.29/0.73    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.29/0.73    inference(cnf_transformation,[],[f1])).
% 1.29/0.73  fof(f1,axiom,(
% 1.29/0.73    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.29/0.73  fof(f62,plain,(
% 1.29/0.73    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.29/0.73    inference(cnf_transformation,[],[f11])).
% 1.29/0.73  fof(f11,axiom,(
% 1.29/0.73    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.29/0.73  fof(f354,plain,(
% 1.29/0.73    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,sK1)),sK1) | k1_xboole_0 = sK1),
% 1.29/0.73    inference(superposition,[],[f267,f350])).
% 1.29/0.73  fof(f350,plain,(
% 1.29/0.73    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 = sK1),
% 1.29/0.73    inference(resolution,[],[f85,f241])).
% 1.29/0.73  fof(f241,plain,(
% 1.29/0.73    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.29/0.73    inference(superposition,[],[f81,f75])).
% 1.29/0.73  fof(f75,plain,(
% 1.29/0.73    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.29/0.73    inference(definition_unfolding,[],[f35,f74,f72])).
% 1.29/0.73  fof(f74,plain,(
% 1.29/0.73    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.29/0.73    inference(definition_unfolding,[],[f38,f71])).
% 1.29/0.73  fof(f38,plain,(
% 1.29/0.73    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.29/0.73    inference(cnf_transformation,[],[f14])).
% 1.29/0.73  fof(f14,axiom,(
% 1.29/0.73    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.29/0.73  fof(f35,plain,(
% 1.29/0.73    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.29/0.73    inference(cnf_transformation,[],[f28])).
% 1.29/0.73  fof(f28,plain,(
% 1.29/0.73    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.29/0.73    inference(ennf_transformation,[],[f24])).
% 1.29/0.73  fof(f24,negated_conjecture,(
% 1.29/0.73    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.29/0.73    inference(negated_conjecture,[],[f23])).
% 1.29/0.73  fof(f23,conjecture,(
% 1.29/0.73    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.29/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.29/0.74  fof(f81,plain,(
% 1.29/0.74    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.29/0.74    inference(definition_unfolding,[],[f43,f72])).
% 1.29/0.74  fof(f43,plain,(
% 1.29/0.74    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.29/0.74    inference(cnf_transformation,[],[f10])).
% 1.29/0.74  fof(f10,axiom,(
% 1.29/0.74    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.29/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.29/0.74  fof(f85,plain,(
% 1.29/0.74    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.29/0.74    inference(definition_unfolding,[],[f58,f74,f74])).
% 1.29/0.74  fof(f58,plain,(
% 1.29/0.74    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.29/0.74    inference(cnf_transformation,[],[f21])).
% 1.29/0.74  fof(f21,axiom,(
% 1.29/0.74    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.29/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.29/0.74  fof(f359,plain,(
% 1.29/0.74    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0 | k1_xboole_0 = sK1) )),
% 1.29/0.74    inference(superposition,[],[f85,f350])).
% 1.29/0.74  fof(f364,plain,(
% 1.29/0.74    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.29/0.74    inference(trivial_inequality_removal,[],[f357])).
% 1.29/0.74  fof(f357,plain,(
% 1.29/0.74    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.29/0.74    inference(superposition,[],[f78,f350])).
% 1.29/0.74  fof(f78,plain,(
% 1.29/0.74    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.29/0.74    inference(definition_unfolding,[],[f32,f74])).
% 1.29/0.74  fof(f32,plain,(
% 1.29/0.74    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.29/0.74    inference(cnf_transformation,[],[f28])).
% 1.29/0.74  fof(f365,plain,(
% 1.29/0.74    sK1 != sK2 | k1_xboole_0 = sK1),
% 1.29/0.74    inference(trivial_inequality_removal,[],[f356])).
% 1.29/0.74  fof(f356,plain,(
% 1.29/0.74    sK1 != sK2 | sK1 != sK1 | k1_xboole_0 = sK1),
% 1.29/0.74    inference(superposition,[],[f76,f350])).
% 1.29/0.74  fof(f76,plain,(
% 1.29/0.74    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.29/0.74    inference(definition_unfolding,[],[f34,f74,f74])).
% 1.29/0.74  fof(f34,plain,(
% 1.29/0.74    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.29/0.74    inference(cnf_transformation,[],[f28])).
% 1.29/0.74  fof(f267,plain,(
% 1.29/0.74    r1_tarski(k5_xboole_0(sK1,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 1.29/0.74    inference(superposition,[],[f93,f75])).
% 1.29/0.74  fof(f93,plain,(
% 1.29/0.74    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 1.29/0.74    inference(backward_demodulation,[],[f82,f62])).
% 1.29/0.74  fof(f82,plain,(
% 1.29/0.74    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 1.29/0.74    inference(definition_unfolding,[],[f44,f73])).
% 1.29/0.74  fof(f44,plain,(
% 1.29/0.74    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.29/0.74    inference(cnf_transformation,[],[f7])).
% 1.29/0.74  fof(f7,axiom,(
% 1.29/0.74    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.29/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.29/0.74  fof(f110,plain,(
% 1.29/0.74    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.29/0.74    inference(unit_resulting_resolution,[],[f107,f56])).
% 1.29/0.74  fof(f56,plain,(
% 1.29/0.74    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.29/0.74    inference(cnf_transformation,[],[f31])).
% 1.29/0.74  fof(f31,plain,(
% 1.29/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.29/0.74    inference(ennf_transformation,[],[f2])).
% 1.29/0.74  fof(f2,axiom,(
% 1.29/0.74    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.29/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.29/0.74  fof(f107,plain,(
% 1.29/0.74    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.29/0.74    inference(duplicate_literal_removal,[],[f106])).
% 1.29/0.74  fof(f106,plain,(
% 1.29/0.74    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.29/0.74    inference(resolution,[],[f49,f86])).
% 1.29/0.74  fof(f86,plain,(
% 1.29/0.74    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.29/0.74    inference(equality_resolution,[],[f40])).
% 1.29/0.74  fof(f40,plain,(
% 1.29/0.74    ( ! [X0] : (r1_xboole_0(X0,X0) | k1_xboole_0 != X0) )),
% 1.29/0.74    inference(cnf_transformation,[],[f29])).
% 1.29/0.74  fof(f29,plain,(
% 1.29/0.74    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.29/0.74    inference(ennf_transformation,[],[f9])).
% 1.29/0.74  fof(f9,axiom,(
% 1.29/0.74    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.29/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.29/0.74  fof(f49,plain,(
% 1.29/0.74    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.29/0.74    inference(cnf_transformation,[],[f30])).
% 1.29/0.74  fof(f30,plain,(
% 1.29/0.74    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.29/0.74    inference(ennf_transformation,[],[f27])).
% 1.29/0.74  fof(f27,plain,(
% 1.29/0.74    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.29/0.74    inference(rectify,[],[f5])).
% 1.29/0.74  fof(f5,axiom,(
% 1.29/0.74    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.29/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.29/0.74  fof(f150,plain,(
% 1.29/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.29/0.74    inference(forward_demodulation,[],[f136,f92])).
% 1.29/0.74  fof(f136,plain,(
% 1.29/0.74    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.29/0.74    inference(superposition,[],[f62,f36])).
% 1.29/0.74  fof(f551,plain,(
% 1.29/0.74    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.29/0.74    inference(global_subsumption,[],[f77,f541])).
% 1.29/0.74  fof(f77,plain,(
% 1.29/0.74    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.29/0.74    inference(definition_unfolding,[],[f33,f74])).
% 1.29/0.74  fof(f33,plain,(
% 1.29/0.74    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.29/0.74    inference(cnf_transformation,[],[f28])).
% 1.29/0.74  % SZS output end Proof for theBenchmark
% 1.29/0.74  % (18473)------------------------------
% 1.29/0.74  % (18473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.29/0.74  % (18473)Termination reason: Refutation
% 1.29/0.74  
% 1.29/0.74  % (18473)Memory used [KB]: 6780
% 1.29/0.74  % (18473)Time elapsed: 0.140 s
% 1.29/0.74  % (18473)------------------------------
% 1.29/0.74  % (18473)------------------------------
% 1.29/0.74  % (18315)Success in time 0.384 s
%------------------------------------------------------------------------------

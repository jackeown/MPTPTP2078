%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:33:31 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   93 (1536 expanded)
%              Number of leaves         :   17 ( 476 expanded)
%              Depth                    :   24
%              Number of atoms          :  131 (1899 expanded)
%              Number of equality atoms :   79 (1388 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1140,plain,(
    $false ),
    inference(resolution,[],[f1121,f79])).

fof(f79,plain,(
    ! [X3,X1] : sP5(X3,X1,X3) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 != X3
      | sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f1121,plain,(
    ~ sP5(sK0,sK1,sK0) ),
    inference(backward_demodulation,[],[f1041,f1089])).

fof(f1089,plain,(
    sK0 = sK2(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f1039,f73])).

fof(f73,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f26])).

fof(f26,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1039,plain,(
    r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f1022,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f1022,plain,(
    ~ r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)) ),
    inference(trivial_inequality_removal,[],[f1021])).

fof(f1021,plain,
    ( k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1)
    | ~ r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)) ),
    inference(backward_demodulation,[],[f131,f1016])).

fof(f1016,plain,(
    ! [X4,X3] : k5_xboole_0(X4,k5_xboole_0(X3,X4)) = X3 ),
    inference(forward_demodulation,[],[f1001,f451])).

fof(f451,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f438,f390])).

fof(f390,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f387,f82])).

fof(f82,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0 ),
    inference(forward_demodulation,[],[f63,f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f63,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f28,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f28,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f387,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f305,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f305,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f62,f277])).

fof(f277,plain,(
    ! [X0] : k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,X0))) = X0 ),
    inference(superposition,[],[f60,f27])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f32,f31,f31])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f25,f58])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f438,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0 ),
    inference(backward_demodulation,[],[f62,f431])).

fof(f431,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f422,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f422,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f409,f36])).

fof(f409,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f403])).

fof(f403,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f320,f390])).

fof(f320,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f302,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f302,plain,(
    ! [X4,X3] :
      ( sP7(X4,k5_xboole_0(X3,X3),X3)
      | ~ r2_hidden(X4,X3) ) ),
    inference(superposition,[],[f80,f277])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1)))
      | sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f55,f31])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f1001,plain,(
    ! [X4,X3] : k5_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X4,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f643,f627])).

fof(f627,plain,(
    ! [X2,X1] : k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2))) ),
    inference(superposition,[],[f550,f43])).

fof(f550,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f549,f27])).

fof(f549,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,k3_xboole_0(X3,X3)) ),
    inference(forward_demodulation,[],[f544,f451])).

fof(f544,plain,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X3,k1_xboole_0))) ),
    inference(superposition,[],[f60,f430])).

fof(f430,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f422,f85])).

fof(f85,plain,(
    ! [X4,X3] :
      ( k3_xboole_0(X4,X3) = X3
      | ~ r1_tarski(X3,X4) ) ),
    inference(superposition,[],[f34,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f643,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f628,f452])).

fof(f452,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,X2) = X2 ),
    inference(backward_demodulation,[],[f434,f451])).

fof(f434,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k1_xboole_0)) = X2 ),
    inference(backward_demodulation,[],[f375,f431])).

fof(f375,plain,(
    ! [X2] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2))) = X2 ),
    inference(superposition,[],[f338,f30])).

fof(f338,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[],[f64,f62])).

fof(f64,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f58,f58])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f628,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f43,f550])).

fof(f131,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))
    | ~ r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f83,f34])).

fof(f83,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f61,f30])).

fof(f61,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))) ),
    inference(definition_unfolding,[],[f24,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f42,f58,f26])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f24,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f1041,plain,(
    ~ sP5(sK2(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)),sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f1038,f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_tarski(X0,X1))
      | ~ sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1038,plain,(
    ~ r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f1022,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:45:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.37  ipcrm: permission denied for id (829292544)
% 0.13/0.37  ipcrm: permission denied for id (829325313)
% 0.22/0.38  ipcrm: permission denied for id (829456393)
% 0.22/0.39  ipcrm: permission denied for id (829587472)
% 0.22/0.39  ipcrm: permission denied for id (829685784)
% 0.22/0.40  ipcrm: permission denied for id (829816860)
% 0.22/0.41  ipcrm: permission denied for id (830013481)
% 0.22/0.42  ipcrm: permission denied for id (830111789)
% 0.22/0.42  ipcrm: permission denied for id (830144560)
% 0.22/0.42  ipcrm: permission denied for id (830177329)
% 0.22/0.43  ipcrm: permission denied for id (830210100)
% 0.22/0.43  ipcrm: permission denied for id (830242870)
% 0.22/0.43  ipcrm: permission denied for id (830275639)
% 0.22/0.44  ipcrm: permission denied for id (830373947)
% 0.22/0.44  ipcrm: permission denied for id (830439486)
% 0.22/0.44  ipcrm: permission denied for id (830537794)
% 0.22/0.45  ipcrm: permission denied for id (830603333)
% 0.22/0.45  ipcrm: permission denied for id (830636102)
% 0.22/0.45  ipcrm: permission denied for id (830701642)
% 0.22/0.46  ipcrm: permission denied for id (830734413)
% 0.22/0.46  ipcrm: permission denied for id (830767183)
% 0.22/0.48  ipcrm: permission denied for id (830931038)
% 0.22/0.48  ipcrm: permission denied for id (830963808)
% 0.22/0.48  ipcrm: permission denied for id (831062115)
% 0.22/0.49  ipcrm: permission denied for id (831094885)
% 0.22/0.50  ipcrm: permission denied for id (831291502)
% 0.22/0.50  ipcrm: permission denied for id (831357041)
% 0.22/0.50  ipcrm: permission denied for id (831389812)
% 0.22/0.51  ipcrm: permission denied for id (831455352)
% 0.22/0.51  ipcrm: permission denied for id (831488121)
% 0.22/0.51  ipcrm: permission denied for id (831520890)
% 0.63/0.65  % (21728)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.63/0.65  % (21703)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.21/0.65  % (21719)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.21/0.66  % (21711)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.21/0.66  % (21699)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.21/0.66  % (21705)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.21/0.67  % (21707)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.21/0.67  % (21721)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.39/0.67  % (21723)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.39/0.67  % (21719)Refutation not found, incomplete strategy% (21719)------------------------------
% 1.39/0.67  % (21719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.67  % (21719)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.67  
% 1.39/0.67  % (21719)Memory used [KB]: 10746
% 1.39/0.67  % (21719)Time elapsed: 0.112 s
% 1.39/0.67  % (21719)------------------------------
% 1.39/0.67  % (21719)------------------------------
% 1.39/0.67  % (21702)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.68  % (21710)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.39/0.68  % (21713)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.39/0.68  % (21709)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.39/0.68  % (21700)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.39/0.68  % (21709)Refutation not found, incomplete strategy% (21709)------------------------------
% 1.39/0.68  % (21709)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.68  % (21709)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.68  
% 1.39/0.68  % (21709)Memory used [KB]: 10618
% 1.39/0.68  % (21709)Time elapsed: 0.109 s
% 1.39/0.68  % (21709)------------------------------
% 1.39/0.68  % (21709)------------------------------
% 1.39/0.68  % (21712)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.39/0.69  % (21721)Refutation not found, incomplete strategy% (21721)------------------------------
% 1.39/0.69  % (21721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.69  % (21726)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.69  % (21706)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.69  % (21707)Refutation not found, incomplete strategy% (21707)------------------------------
% 1.39/0.69  % (21707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.69  % (21707)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.69  
% 1.39/0.69  % (21707)Memory used [KB]: 10618
% 1.39/0.69  % (21707)Time elapsed: 0.120 s
% 1.39/0.69  % (21707)------------------------------
% 1.39/0.69  % (21707)------------------------------
% 1.39/0.69  % (21717)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.39/0.69  % (21704)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.39/0.69  % (21718)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.39/0.69  % (21721)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.69  
% 1.39/0.69  % (21721)Memory used [KB]: 10746
% 1.39/0.69  % (21721)Time elapsed: 0.114 s
% 1.39/0.69  % (21721)------------------------------
% 1.39/0.69  % (21721)------------------------------
% 1.39/0.69  % (21701)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.39/0.70  % (21701)Refutation not found, incomplete strategy% (21701)------------------------------
% 1.39/0.70  % (21701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.70  % (21701)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.70  
% 1.39/0.70  % (21701)Memory used [KB]: 10746
% 1.39/0.70  % (21701)Time elapsed: 0.130 s
% 1.39/0.70  % (21701)------------------------------
% 1.39/0.70  % (21701)------------------------------
% 1.39/0.70  % (21720)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.39/0.70  % (21716)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.39/0.70  % (21720)Refutation not found, incomplete strategy% (21720)------------------------------
% 1.39/0.70  % (21720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.70  % (21720)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.70  
% 1.39/0.70  % (21720)Memory used [KB]: 1663
% 1.39/0.70  % (21720)Time elapsed: 0.093 s
% 1.39/0.70  % (21720)------------------------------
% 1.39/0.70  % (21720)------------------------------
% 1.39/0.70  % (21716)Refutation not found, incomplete strategy% (21716)------------------------------
% 1.39/0.70  % (21716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.70  % (21716)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.70  
% 1.39/0.70  % (21716)Memory used [KB]: 10618
% 1.39/0.70  % (21716)Time elapsed: 0.131 s
% 1.39/0.70  % (21716)------------------------------
% 1.39/0.70  % (21716)------------------------------
% 1.39/0.70  % (21727)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.70  % (21722)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.39/0.70  % (21722)Refutation not found, incomplete strategy% (21722)------------------------------
% 1.39/0.70  % (21722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.70  % (21722)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.70  
% 1.39/0.70  % (21722)Memory used [KB]: 1663
% 1.39/0.70  % (21722)Time elapsed: 0.141 s
% 1.39/0.70  % (21722)------------------------------
% 1.39/0.70  % (21722)------------------------------
% 1.39/0.70  % (21725)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.71  % (21708)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.39/0.71  % (21715)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.39/0.71  % (21724)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.74/0.72  % (21714)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.74/0.73  % (21723)Refutation found. Thanks to Tanya!
% 1.74/0.73  % SZS status Theorem for theBenchmark
% 1.74/0.73  % SZS output start Proof for theBenchmark
% 1.74/0.73  fof(f1140,plain,(
% 1.74/0.73    $false),
% 1.74/0.73    inference(resolution,[],[f1121,f79])).
% 1.74/0.73  fof(f79,plain,(
% 1.74/0.73    ( ! [X3,X1] : (sP5(X3,X1,X3)) )),
% 1.74/0.73    inference(equality_resolution,[],[f44])).
% 1.74/0.73  fof(f44,plain,(
% 1.74/0.73    ( ! [X0,X3,X1] : (X0 != X3 | sP5(X3,X1,X0)) )),
% 1.74/0.73    inference(cnf_transformation,[],[f14])).
% 1.74/0.73  fof(f14,axiom,(
% 1.74/0.73    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.74/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.74/0.73  fof(f1121,plain,(
% 1.74/0.73    ~sP5(sK0,sK1,sK0)),
% 1.74/0.73    inference(backward_demodulation,[],[f1041,f1089])).
% 1.74/0.73  fof(f1089,plain,(
% 1.74/0.73    sK0 = sK2(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))),
% 1.74/0.73    inference(unit_resulting_resolution,[],[f1039,f73])).
% 1.74/0.73  fof(f73,plain,(
% 1.74/0.73    ( ! [X2,X0] : (~r2_hidden(X2,k2_tarski(X0,X0)) | X0 = X2) )),
% 1.74/0.73    inference(equality_resolution,[],[f67])).
% 1.74/0.73  fof(f67,plain,(
% 1.74/0.73    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_tarski(X0,X0) != X1) )),
% 1.74/0.73    inference(definition_unfolding,[],[f39,f26])).
% 1.74/0.73  fof(f26,plain,(
% 1.74/0.73    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.74/0.73    inference(cnf_transformation,[],[f16])).
% 1.74/0.73  fof(f16,axiom,(
% 1.74/0.73    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.74/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.74/0.73  fof(f39,plain,(
% 1.74/0.73    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.74/0.73    inference(cnf_transformation,[],[f13])).
% 1.74/0.73  fof(f13,axiom,(
% 1.74/0.73    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.74/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.74/0.73  fof(f1039,plain,(
% 1.74/0.73    r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK0))),
% 1.74/0.73    inference(unit_resulting_resolution,[],[f1022,f36])).
% 1.74/0.73  fof(f36,plain,(
% 1.74/0.73    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.74/0.73    inference(cnf_transformation,[],[f23])).
% 1.74/0.73  fof(f23,plain,(
% 1.74/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.74/0.73    inference(ennf_transformation,[],[f3])).
% 1.74/0.73  fof(f3,axiom,(
% 1.74/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.74/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.74/0.73  fof(f1022,plain,(
% 1.74/0.73    ~r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))),
% 1.74/0.73    inference(trivial_inequality_removal,[],[f1021])).
% 1.74/0.73  fof(f1021,plain,(
% 1.74/0.73    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK1) | ~r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))),
% 1.74/0.73    inference(backward_demodulation,[],[f131,f1016])).
% 1.74/0.73  fof(f1016,plain,(
% 1.74/0.73    ( ! [X4,X3] : (k5_xboole_0(X4,k5_xboole_0(X3,X4)) = X3) )),
% 1.74/0.73    inference(forward_demodulation,[],[f1001,f451])).
% 1.74/0.73  fof(f451,plain,(
% 1.74/0.73    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.74/0.73    inference(forward_demodulation,[],[f438,f390])).
% 1.74/0.73  fof(f390,plain,(
% 1.74/0.73    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.74/0.73    inference(forward_demodulation,[],[f387,f82])).
% 1.74/0.73  fof(f82,plain,(
% 1.74/0.73    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,X0)) = X0) )),
% 1.74/0.73    inference(forward_demodulation,[],[f63,f27])).
% 1.74/0.73  fof(f27,plain,(
% 1.74/0.73    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.74/0.73    inference(cnf_transformation,[],[f19])).
% 1.74/0.73  fof(f19,plain,(
% 1.74/0.73    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.74/0.73    inference(rectify,[],[f6])).
% 1.74/0.73  fof(f6,axiom,(
% 1.74/0.73    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.74/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.74/0.73  fof(f63,plain,(
% 1.74/0.73    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X0))) = X0) )),
% 1.74/0.73    inference(definition_unfolding,[],[f28,f58])).
% 1.74/0.73  fof(f58,plain,(
% 1.74/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.74/0.73    inference(definition_unfolding,[],[f33,f31])).
% 1.74/0.73  fof(f31,plain,(
% 1.74/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.74/0.73    inference(cnf_transformation,[],[f7])).
% 1.74/0.73  fof(f7,axiom,(
% 1.74/0.73    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.74/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.74/0.73  fof(f33,plain,(
% 1.74/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.74/0.73    inference(cnf_transformation,[],[f12])).
% 1.74/0.73  fof(f12,axiom,(
% 1.74/0.73    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.74/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.74/0.73  fof(f28,plain,(
% 1.74/0.73    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.74/0.73    inference(cnf_transformation,[],[f20])).
% 1.74/0.73  fof(f20,plain,(
% 1.74/0.73    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.74/0.73    inference(rectify,[],[f5])).
% 1.74/0.73  fof(f5,axiom,(
% 1.74/0.73    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.74/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.74/0.73  fof(f387,plain,(
% 1.74/0.73    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,k1_xboole_0))),
% 1.74/0.73    inference(superposition,[],[f305,f43])).
% 1.74/0.73  fof(f43,plain,(
% 1.74/0.73    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.74/0.73    inference(cnf_transformation,[],[f11])).
% 1.74/0.73  fof(f11,axiom,(
% 1.74/0.73    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.74/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.74/0.73  fof(f305,plain,(
% 1.74/0.73    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 1.74/0.73    inference(superposition,[],[f62,f277])).
% 1.74/0.73  fof(f277,plain,(
% 1.74/0.73    ( ! [X0] : (k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,X0))) = X0) )),
% 1.74/0.73    inference(superposition,[],[f60,f27])).
% 1.74/0.73  fof(f60,plain,(
% 1.74/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 1.74/0.73    inference(definition_unfolding,[],[f32,f31,f31])).
% 1.74/0.73  fof(f32,plain,(
% 1.74/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.74/0.73    inference(cnf_transformation,[],[f10])).
% 1.74/0.73  fof(f10,axiom,(
% 1.74/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.74/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.74/0.73  fof(f62,plain,(
% 1.74/0.73    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 1.74/0.73    inference(definition_unfolding,[],[f25,f58])).
% 1.74/0.73  fof(f25,plain,(
% 1.74/0.73    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.74/0.73    inference(cnf_transformation,[],[f8])).
% 1.74/0.73  fof(f8,axiom,(
% 1.74/0.73    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.74/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.74/0.73  fof(f438,plain,(
% 1.74/0.73    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k1_xboole_0)) = X0) )),
% 1.74/0.73    inference(backward_demodulation,[],[f62,f431])).
% 1.74/0.73  fof(f431,plain,(
% 1.74/0.73    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.74/0.73    inference(unit_resulting_resolution,[],[f422,f34])).
% 1.74/0.73  fof(f34,plain,(
% 1.74/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.74/0.73    inference(cnf_transformation,[],[f22])).
% 1.74/0.73  fof(f22,plain,(
% 1.74/0.73    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.74/0.73    inference(ennf_transformation,[],[f9])).
% 1.74/0.73  fof(f9,axiom,(
% 1.74/0.73    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.74/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.74/0.73  fof(f422,plain,(
% 1.74/0.73    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.74/0.73    inference(unit_resulting_resolution,[],[f409,f36])).
% 1.74/0.73  fof(f409,plain,(
% 1.74/0.73    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.74/0.73    inference(duplicate_literal_removal,[],[f403])).
% 1.74/0.73  fof(f403,plain,(
% 1.74/0.73    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,k1_xboole_0)) )),
% 1.74/0.73    inference(superposition,[],[f320,f390])).
% 1.74/0.73  fof(f320,plain,(
% 1.74/0.73    ( ! [X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X1)) | ~r2_hidden(X0,X1)) )),
% 1.74/0.73    inference(resolution,[],[f302,f53])).
% 1.74/0.73  fof(f53,plain,(
% 1.74/0.73    ( ! [X0,X3,X1] : (~sP7(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 1.74/0.73    inference(cnf_transformation,[],[f4])).
% 1.74/0.73  fof(f4,axiom,(
% 1.74/0.73    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.74/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.74/0.73  fof(f302,plain,(
% 1.74/0.73    ( ! [X4,X3] : (sP7(X4,k5_xboole_0(X3,X3),X3) | ~r2_hidden(X4,X3)) )),
% 1.74/0.73    inference(superposition,[],[f80,f277])).
% 1.74/0.73  fof(f80,plain,(
% 1.74/0.73    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_xboole_0(X0,k3_xboole_0(X0,X1))) | sP7(X3,X1,X0)) )),
% 1.74/0.73    inference(equality_resolution,[],[f71])).
% 1.74/0.73  fof(f71,plain,(
% 1.74/0.73    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k3_xboole_0(X0,X1)) != X2) )),
% 1.74/0.73    inference(definition_unfolding,[],[f55,f31])).
% 1.74/0.73  fof(f55,plain,(
% 1.74/0.73    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.74/0.73    inference(cnf_transformation,[],[f4])).
% 1.74/0.73  fof(f1001,plain,(
% 1.74/0.73    ( ! [X4,X3] : (k5_xboole_0(X3,k1_xboole_0) = k5_xboole_0(X4,k5_xboole_0(X3,X4))) )),
% 1.74/0.73    inference(superposition,[],[f643,f627])).
% 1.74/0.73  fof(f627,plain,(
% 1.74/0.73    ( ! [X2,X1] : (k1_xboole_0 = k5_xboole_0(X1,k5_xboole_0(X2,k5_xboole_0(X1,X2)))) )),
% 1.74/0.73    inference(superposition,[],[f550,f43])).
% 1.74/0.73  fof(f550,plain,(
% 1.74/0.73    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) )),
% 1.74/0.73    inference(forward_demodulation,[],[f549,f27])).
% 1.74/0.73  fof(f549,plain,(
% 1.74/0.73    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,k3_xboole_0(X3,X3))) )),
% 1.74/0.73    inference(forward_demodulation,[],[f544,f451])).
% 1.74/0.73  fof(f544,plain,(
% 1.74/0.73    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,k3_xboole_0(X3,k5_xboole_0(X3,k1_xboole_0)))) )),
% 1.74/0.73    inference(superposition,[],[f60,f430])).
% 1.74/0.73  fof(f430,plain,(
% 1.74/0.74    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.74/0.74    inference(unit_resulting_resolution,[],[f422,f85])).
% 1.74/0.74  fof(f85,plain,(
% 1.74/0.74    ( ! [X4,X3] : (k3_xboole_0(X4,X3) = X3 | ~r1_tarski(X3,X4)) )),
% 1.74/0.74    inference(superposition,[],[f34,f30])).
% 1.74/0.74  fof(f30,plain,(
% 1.74/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.74/0.74    inference(cnf_transformation,[],[f2])).
% 1.74/0.74  fof(f2,axiom,(
% 1.74/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.74/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.74/0.74  fof(f643,plain,(
% 1.74/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.74/0.74    inference(forward_demodulation,[],[f628,f452])).
% 1.74/0.74  fof(f452,plain,(
% 1.74/0.74    ( ! [X2] : (k5_xboole_0(k1_xboole_0,X2) = X2) )),
% 1.74/0.74    inference(backward_demodulation,[],[f434,f451])).
% 1.74/0.74  fof(f434,plain,(
% 1.74/0.74    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k1_xboole_0)) = X2) )),
% 1.74/0.74    inference(backward_demodulation,[],[f375,f431])).
% 1.74/0.74  fof(f375,plain,(
% 1.74/0.74    ( ! [X2] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X2,k3_xboole_0(k1_xboole_0,X2))) = X2) )),
% 1.74/0.74    inference(superposition,[],[f338,f30])).
% 1.74/0.74  fof(f338,plain,(
% 1.74/0.74    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) = X0) )),
% 1.74/0.74    inference(superposition,[],[f64,f62])).
% 1.74/0.74  fof(f64,plain,(
% 1.74/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.74/0.74    inference(definition_unfolding,[],[f29,f58,f58])).
% 1.74/0.74  fof(f29,plain,(
% 1.74/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.74/0.74    inference(cnf_transformation,[],[f1])).
% 1.74/0.74  fof(f1,axiom,(
% 1.74/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.74/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.74/0.74  fof(f628,plain,(
% 1.74/0.74    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.74/0.74    inference(superposition,[],[f43,f550])).
% 1.74/0.74  fof(f131,plain,(
% 1.74/0.74    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))) | ~r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))),
% 1.74/0.74    inference(superposition,[],[f83,f34])).
% 1.74/0.74  fof(f83,plain,(
% 1.74/0.74    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))))),
% 1.74/0.74    inference(backward_demodulation,[],[f61,f30])).
% 1.74/0.74  fof(f61,plain,(
% 1.74/0.74    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))))),
% 1.74/0.74    inference(definition_unfolding,[],[f24,f59])).
% 1.74/0.74  fof(f59,plain,(
% 1.74/0.74    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X2),k3_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))))) )),
% 1.74/0.74    inference(definition_unfolding,[],[f42,f58,f26])).
% 1.74/0.74  fof(f42,plain,(
% 1.74/0.74    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.74/0.74    inference(cnf_transformation,[],[f15])).
% 1.74/0.74  fof(f15,axiom,(
% 1.74/0.74    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.74/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 1.74/0.74  fof(f24,plain,(
% 1.74/0.74    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 1.74/0.74    inference(cnf_transformation,[],[f21])).
% 1.74/0.74  fof(f21,plain,(
% 1.74/0.74    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 1.74/0.74    inference(ennf_transformation,[],[f18])).
% 1.74/0.74  fof(f18,negated_conjecture,(
% 1.74/0.74    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.74/0.74    inference(negated_conjecture,[],[f17])).
% 1.74/0.74  fof(f17,conjecture,(
% 1.74/0.74    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.74/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.74/0.74  fof(f1041,plain,(
% 1.74/0.74    ~sP5(sK2(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)),sK1,sK0)),
% 1.74/0.74    inference(unit_resulting_resolution,[],[f1038,f77])).
% 1.74/0.74  fof(f77,plain,(
% 1.74/0.74    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_tarski(X0,X1)) | ~sP5(X3,X1,X0)) )),
% 1.74/0.74    inference(equality_resolution,[],[f47])).
% 1.74/0.74  fof(f47,plain,(
% 1.74/0.74    ( ! [X2,X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.74/0.74    inference(cnf_transformation,[],[f14])).
% 1.74/0.74  fof(f1038,plain,(
% 1.74/0.74    ~r2_hidden(sK2(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 1.74/0.74    inference(unit_resulting_resolution,[],[f1022,f37])).
% 1.74/0.74  fof(f37,plain,(
% 1.74/0.74    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.74/0.74    inference(cnf_transformation,[],[f23])).
% 1.74/0.74  % SZS output end Proof for theBenchmark
% 1.74/0.74  % (21723)------------------------------
% 1.74/0.74  % (21723)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.74  % (21723)Termination reason: Refutation
% 1.74/0.74  
% 1.74/0.74  % (21723)Memory used [KB]: 7036
% 1.74/0.74  % (21723)Time elapsed: 0.172 s
% 1.74/0.74  % (21723)------------------------------
% 1.74/0.74  % (21723)------------------------------
% 1.74/0.74  % (21565)Success in time 0.371 s
%------------------------------------------------------------------------------

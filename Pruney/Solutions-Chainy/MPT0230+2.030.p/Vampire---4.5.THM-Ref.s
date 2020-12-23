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
% DateTime   : Thu Dec  3 12:36:38 EST 2020

% Result     : Theorem 1.72s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 217 expanded)
%              Number of leaves         :   18 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :  121 ( 281 expanded)
%              Number of equality atoms :   86 ( 227 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f902,plain,(
    $false ),
    inference(subsumption_resolution,[],[f899,f159])).

fof(f159,plain,(
    ~ r2_hidden(sK0,k2_tarski(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f104,f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f104,plain,(
    ~ sP4(sK0,sK2,sK1) ),
    inference(unit_resulting_resolution,[],[f29,f30,f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & X0 != X1
      & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X2
          & X0 != X1
          & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X2
        & X0 != X1
        & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

fof(f29,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f899,plain,(
    r2_hidden(sK0,k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f276,f842])).

fof(f842,plain,(
    k2_tarski(sK1,sK2) = k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
    inference(forward_demodulation,[],[f824,f49])).

fof(f49,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f824,plain,(
    k5_xboole_0(k2_tarski(sK1,sK2),k1_xboole_0) = k3_enumset1(sK1,sK1,sK1,sK2,sK0) ),
    inference(superposition,[],[f247,f310])).

fof(f310,plain,(
    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) ),
    inference(backward_demodulation,[],[f232,f305])).

fof(f305,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(backward_demodulation,[],[f207,f304])).

fof(f304,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f296,f49])).

fof(f296,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f124,f214])).

fof(f214,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(forward_demodulation,[],[f211,f49])).

fof(f211,plain,(
    ! [X2] : k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f64,f116])).

fof(f116,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f32,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f31,f45])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f124,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))) ),
    inference(superposition,[],[f64,f69])).

fof(f69,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f47,f45,f45])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f207,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f116,f69])).

fof(f232,plain,(
    k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    inference(forward_demodulation,[],[f230,f122])).

fof(f122,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f64,f70])).

fof(f70,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f48,f45])).

fof(f48,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f230,plain,(
    k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    inference(superposition,[],[f64,f117])).

fof(f117,plain,(
    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f66,f67])).

fof(f66,plain,(
    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f28,f43])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f247,plain,(
    ! [X6,X8,X7] : k3_enumset1(X6,X6,X6,X7,X8) = k5_xboole_0(k2_tarski(X6,X7),k4_xboole_0(k2_tarski(X8,X8),k2_tarski(X6,X7))) ),
    inference(superposition,[],[f88,f164])).

fof(f164,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X1,X0) ),
    inference(superposition,[],[f71,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X0),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f42,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) ),
    inference(definition_unfolding,[],[f41,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f51,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f88,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k5_xboole_0(k3_enumset1(X1,X1,X0,X2,X0),k4_xboole_0(k2_tarski(X3,X3),k3_enumset1(X1,X1,X0,X2,X0))) ),
    inference(forward_demodulation,[],[f87,f71])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) = k5_xboole_0(k3_enumset1(X1,X1,X0,X2,X0),k4_xboole_0(k2_tarski(X3,X3),k3_enumset1(X1,X1,X0,X2,X0))) ),
    inference(backward_demodulation,[],[f68,f71])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) = k5_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))))) ),
    inference(definition_unfolding,[],[f44,f63,f50,f62,f43])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

fof(f276,plain,(
    ! [X14,X12,X13] : r2_hidden(X14,k3_enumset1(X13,X13,X13,X12,X14)) ),
    inference(superposition,[],[f129,f169])).

fof(f169,plain,(
    ! [X4,X2,X3] : k3_enumset1(X2,X2,X3,X4,X3) = k3_enumset1(X3,X3,X3,X2,X4) ),
    inference(superposition,[],[f89,f71])).

fof(f89,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(forward_demodulation,[],[f72,f71])).

fof(f72,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f52,f62,f63])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f129,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k3_enumset1(X1,X1,X2,X0,X2)) ),
    inference(unit_resulting_resolution,[],[f84,f93])).

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k3_enumset1(X1,X1,X0,X2,X0))
      | ~ sP6(X4,X2,X1,X0) ) ),
    inference(forward_demodulation,[],[f83,f71])).

fof(f83,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | r2_hidden(X4,k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0)))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP6(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) != X3 ) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f57,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP6(X4,X2,X1,X0)
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f84,plain,(
    ! [X4,X0,X1] : sP6(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP6(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:26:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (30619)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (30612)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (30614)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (30620)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (30630)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.52  % (30610)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (30629)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (30627)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (30613)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (30624)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (30638)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (30627)Refutation not found, incomplete strategy% (30627)------------------------------
% 0.21/0.53  % (30627)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30632)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (30627)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30627)Memory used [KB]: 1791
% 0.21/0.53  % (30627)Time elapsed: 0.120 s
% 0.21/0.53  % (30627)------------------------------
% 0.21/0.53  % (30627)------------------------------
% 0.21/0.53  % (30622)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (30622)Refutation not found, incomplete strategy% (30622)------------------------------
% 0.21/0.53  % (30622)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30622)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30617)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (30622)Memory used [KB]: 10618
% 0.21/0.53  % (30622)Time elapsed: 0.130 s
% 0.21/0.53  % (30622)------------------------------
% 0.21/0.53  % (30622)------------------------------
% 0.21/0.54  % (30633)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (30634)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (30611)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (30625)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (30611)Refutation not found, incomplete strategy% (30611)------------------------------
% 0.21/0.54  % (30611)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (30611)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (30611)Memory used [KB]: 1663
% 0.21/0.54  % (30611)Time elapsed: 0.126 s
% 0.21/0.54  % (30611)------------------------------
% 0.21/0.54  % (30611)------------------------------
% 0.21/0.54  % (30618)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (30623)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (30615)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.54  % (30621)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (30635)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (30616)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (30636)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (30621)Refutation not found, incomplete strategy% (30621)------------------------------
% 0.21/0.55  % (30621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30621)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30621)Memory used [KB]: 6268
% 0.21/0.55  % (30621)Time elapsed: 0.134 s
% 0.21/0.55  % (30621)------------------------------
% 0.21/0.55  % (30621)------------------------------
% 0.21/0.55  % (30635)Refutation not found, incomplete strategy% (30635)------------------------------
% 0.21/0.55  % (30635)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30626)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (30635)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30635)Memory used [KB]: 6140
% 0.21/0.55  % (30635)Time elapsed: 0.141 s
% 0.21/0.55  % (30635)------------------------------
% 0.21/0.55  % (30635)------------------------------
% 0.21/0.55  % (30636)Refutation not found, incomplete strategy% (30636)------------------------------
% 0.21/0.55  % (30636)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30636)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30636)Memory used [KB]: 6268
% 0.21/0.55  % (30636)Time elapsed: 0.137 s
% 0.21/0.55  % (30636)------------------------------
% 0.21/0.55  % (30636)------------------------------
% 0.21/0.55  % (30626)Refutation not found, incomplete strategy% (30626)------------------------------
% 0.21/0.55  % (30626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30626)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30626)Memory used [KB]: 10618
% 0.21/0.55  % (30626)Time elapsed: 0.138 s
% 0.21/0.55  % (30626)------------------------------
% 0.21/0.55  % (30626)------------------------------
% 0.21/0.55  % (30634)Refutation not found, incomplete strategy% (30634)------------------------------
% 0.21/0.55  % (30634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30634)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30639)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (30639)Refutation not found, incomplete strategy% (30639)------------------------------
% 0.21/0.55  % (30639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30639)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30639)Memory used [KB]: 1663
% 0.21/0.55  % (30639)Time elapsed: 0.001 s
% 0.21/0.55  % (30639)------------------------------
% 0.21/0.55  % (30639)------------------------------
% 0.21/0.55  % (30631)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (30624)Refutation not found, incomplete strategy% (30624)------------------------------
% 0.21/0.55  % (30624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30624)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (30624)Memory used [KB]: 1791
% 0.21/0.55  % (30624)Time elapsed: 0.090 s
% 0.21/0.55  % (30624)------------------------------
% 0.21/0.55  % (30624)------------------------------
% 0.21/0.55  % (30628)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.56  % (30634)Memory used [KB]: 10746
% 1.53/0.56  % (30628)Refutation not found, incomplete strategy% (30628)------------------------------
% 1.53/0.56  % (30628)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.56  % (30628)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.56  
% 1.53/0.56  % (30628)Memory used [KB]: 1663
% 1.53/0.56  % (30628)Time elapsed: 0.161 s
% 1.53/0.56  % (30628)------------------------------
% 1.53/0.56  % (30628)------------------------------
% 1.53/0.56  % (30634)Time elapsed: 0.139 s
% 1.53/0.56  % (30634)------------------------------
% 1.53/0.56  % (30634)------------------------------
% 1.53/0.57  % (30637)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.53/0.57  % (30637)Refutation not found, incomplete strategy% (30637)------------------------------
% 1.53/0.57  % (30637)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (30637)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (30637)Memory used [KB]: 6140
% 1.53/0.57  % (30637)Time elapsed: 0.154 s
% 1.53/0.57  % (30637)------------------------------
% 1.53/0.57  % (30637)------------------------------
% 1.72/0.58  % (30629)Refutation found. Thanks to Tanya!
% 1.72/0.58  % SZS status Theorem for theBenchmark
% 1.72/0.59  % SZS output start Proof for theBenchmark
% 1.72/0.59  fof(f902,plain,(
% 1.72/0.59    $false),
% 1.72/0.59    inference(subsumption_resolution,[],[f899,f159])).
% 1.72/0.59  fof(f159,plain,(
% 1.72/0.59    ~r2_hidden(sK0,k2_tarski(sK1,sK2))),
% 1.72/0.59    inference(unit_resulting_resolution,[],[f104,f78])).
% 1.72/0.59  fof(f78,plain,(
% 1.72/0.59    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | sP4(X3,X1,X0)) )),
% 1.72/0.59    inference(equality_resolution,[],[f38])).
% 1.72/0.59  fof(f38,plain,(
% 1.72/0.59    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.72/0.59    inference(cnf_transformation,[],[f10])).
% 1.72/0.59  fof(f10,axiom,(
% 1.72/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.72/0.59  fof(f104,plain,(
% 1.72/0.59    ~sP4(sK0,sK2,sK1)),
% 1.72/0.59    inference(unit_resulting_resolution,[],[f29,f30,f36])).
% 1.72/0.59  fof(f36,plain,(
% 1.72/0.59    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 1.72/0.59    inference(cnf_transformation,[],[f10])).
% 1.72/0.59  fof(f30,plain,(
% 1.72/0.59    sK0 != sK2),
% 1.72/0.59    inference(cnf_transformation,[],[f25])).
% 1.72/0.59  fof(f25,plain,(
% 1.72/0.59    ? [X0,X1,X2] : (X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.72/0.59    inference(ennf_transformation,[],[f23])).
% 1.72/0.59  fof(f23,negated_conjecture,(
% 1.72/0.59    ~! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.72/0.59    inference(negated_conjecture,[],[f22])).
% 1.72/0.59  fof(f22,conjecture,(
% 1.72/0.59    ! [X0,X1,X2] : ~(X0 != X2 & X0 != X1 & r1_tarski(k1_tarski(X0),k2_tarski(X1,X2)))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).
% 1.72/0.59  fof(f29,plain,(
% 1.72/0.59    sK0 != sK1),
% 1.72/0.59    inference(cnf_transformation,[],[f25])).
% 1.72/0.59  fof(f899,plain,(
% 1.72/0.59    r2_hidden(sK0,k2_tarski(sK1,sK2))),
% 1.72/0.59    inference(superposition,[],[f276,f842])).
% 1.72/0.59  fof(f842,plain,(
% 1.72/0.59    k2_tarski(sK1,sK2) = k3_enumset1(sK1,sK1,sK1,sK2,sK0)),
% 1.72/0.59    inference(forward_demodulation,[],[f824,f49])).
% 1.72/0.59  fof(f49,plain,(
% 1.72/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.72/0.59    inference(cnf_transformation,[],[f7])).
% 1.72/0.59  fof(f7,axiom,(
% 1.72/0.59    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.72/0.59  fof(f824,plain,(
% 1.72/0.59    k5_xboole_0(k2_tarski(sK1,sK2),k1_xboole_0) = k3_enumset1(sK1,sK1,sK1,sK2,sK0)),
% 1.72/0.59    inference(superposition,[],[f247,f310])).
% 1.72/0.59  fof(f310,plain,(
% 1.72/0.59    k1_xboole_0 = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))),
% 1.72/0.59    inference(backward_demodulation,[],[f232,f305])).
% 1.72/0.59  fof(f305,plain,(
% 1.72/0.59    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 1.72/0.59    inference(backward_demodulation,[],[f207,f304])).
% 1.72/0.59  fof(f304,plain,(
% 1.72/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.72/0.59    inference(forward_demodulation,[],[f296,f49])).
% 1.72/0.59  fof(f296,plain,(
% 1.72/0.59    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 1.72/0.59    inference(superposition,[],[f124,f214])).
% 1.72/0.59  fof(f214,plain,(
% 1.72/0.59    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 1.72/0.59    inference(forward_demodulation,[],[f211,f49])).
% 1.72/0.59  fof(f211,plain,(
% 1.72/0.59    ( ! [X2] : (k4_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 1.72/0.59    inference(superposition,[],[f64,f116])).
% 1.72/0.59  fof(f116,plain,(
% 1.72/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 1.72/0.59    inference(unit_resulting_resolution,[],[f32,f67])).
% 1.72/0.59  fof(f67,plain,(
% 1.72/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.72/0.59    inference(definition_unfolding,[],[f31,f45])).
% 1.72/0.59  fof(f45,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f6])).
% 1.72/0.59  fof(f6,axiom,(
% 1.72/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.72/0.59  fof(f31,plain,(
% 1.72/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.72/0.59    inference(cnf_transformation,[],[f26])).
% 1.72/0.59  fof(f26,plain,(
% 1.72/0.59    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.72/0.59    inference(ennf_transformation,[],[f4])).
% 1.72/0.59  fof(f4,axiom,(
% 1.72/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.72/0.59  fof(f32,plain,(
% 1.72/0.59    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f5])).
% 1.72/0.59  fof(f5,axiom,(
% 1.72/0.59    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.72/0.59  fof(f64,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.72/0.59    inference(definition_unfolding,[],[f46,f45])).
% 1.72/0.59  fof(f46,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f3])).
% 1.72/0.59  fof(f3,axiom,(
% 1.72/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.72/0.59  fof(f124,plain,(
% 1.72/0.59    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) )),
% 1.72/0.59    inference(superposition,[],[f64,f69])).
% 1.72/0.59  fof(f69,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.72/0.59    inference(definition_unfolding,[],[f47,f45,f45])).
% 1.72/0.59  fof(f47,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f1])).
% 1.72/0.59  fof(f1,axiom,(
% 1.72/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.72/0.59  fof(f207,plain,(
% 1.72/0.59    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 1.72/0.59    inference(superposition,[],[f116,f69])).
% 1.72/0.59  fof(f232,plain,(
% 1.72/0.59    k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 1.72/0.59    inference(forward_demodulation,[],[f230,f122])).
% 1.72/0.59  fof(f122,plain,(
% 1.72/0.59    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 1.72/0.59    inference(superposition,[],[f64,f70])).
% 1.72/0.59  fof(f70,plain,(
% 1.72/0.59    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.72/0.59    inference(definition_unfolding,[],[f48,f45])).
% 1.72/0.59  fof(f48,plain,(
% 1.72/0.59    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.72/0.59    inference(cnf_transformation,[],[f24])).
% 1.72/0.59  fof(f24,plain,(
% 1.72/0.59    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.72/0.59    inference(rectify,[],[f2])).
% 1.72/0.59  fof(f2,axiom,(
% 1.72/0.59    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.72/0.59  fof(f230,plain,(
% 1.72/0.59    k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)) = k5_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 1.72/0.59    inference(superposition,[],[f64,f117])).
% 1.72/0.59  fof(f117,plain,(
% 1.72/0.59    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2)))),
% 1.72/0.59    inference(unit_resulting_resolution,[],[f66,f67])).
% 1.72/0.59  fof(f66,plain,(
% 1.72/0.59    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK1,sK2))),
% 1.72/0.59    inference(definition_unfolding,[],[f28,f43])).
% 1.72/0.59  fof(f43,plain,(
% 1.72/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f14])).
% 1.72/0.59  fof(f14,axiom,(
% 1.72/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.72/0.59  fof(f28,plain,(
% 1.72/0.59    r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))),
% 1.72/0.59    inference(cnf_transformation,[],[f25])).
% 1.72/0.59  fof(f247,plain,(
% 1.72/0.59    ( ! [X6,X8,X7] : (k3_enumset1(X6,X6,X6,X7,X8) = k5_xboole_0(k2_tarski(X6,X7),k4_xboole_0(k2_tarski(X8,X8),k2_tarski(X6,X7)))) )),
% 1.72/0.59    inference(superposition,[],[f88,f164])).
% 1.72/0.59  fof(f164,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X1,X0)) )),
% 1.72/0.59    inference(superposition,[],[f71,f65])).
% 1.72/0.59  fof(f65,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X0),k2_tarski(X0,X0)))) )),
% 1.72/0.59    inference(definition_unfolding,[],[f42,f62])).
% 1.72/0.59  fof(f62,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0)))) )),
% 1.72/0.59    inference(definition_unfolding,[],[f41,f50])).
% 1.72/0.59  fof(f50,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f8])).
% 1.72/0.59  fof(f8,axiom,(
% 1.72/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.72/0.59  fof(f41,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f12])).
% 1.72/0.59  fof(f12,axiom,(
% 1.72/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 1.72/0.59  fof(f42,plain,(
% 1.72/0.59    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f15])).
% 1.72/0.59  fof(f15,axiom,(
% 1.72/0.59    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.72/0.59  fof(f71,plain,(
% 1.72/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) )),
% 1.72/0.59    inference(definition_unfolding,[],[f51,f63])).
% 1.72/0.59  fof(f63,plain,(
% 1.72/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1)))) )),
% 1.72/0.59    inference(definition_unfolding,[],[f33,f50])).
% 1.72/0.59  fof(f33,plain,(
% 1.72/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f11])).
% 1.72/0.59  fof(f11,axiom,(
% 1.72/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 1.72/0.59  fof(f51,plain,(
% 1.72/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f17])).
% 1.72/0.59  fof(f17,axiom,(
% 1.72/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.72/0.59  fof(f88,plain,(
% 1.72/0.59    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k5_xboole_0(k3_enumset1(X1,X1,X0,X2,X0),k4_xboole_0(k2_tarski(X3,X3),k3_enumset1(X1,X1,X0,X2,X0)))) )),
% 1.72/0.59    inference(forward_demodulation,[],[f87,f71])).
% 1.72/0.59  fof(f87,plain,(
% 1.72/0.59    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) = k5_xboole_0(k3_enumset1(X1,X1,X0,X2,X0),k4_xboole_0(k2_tarski(X3,X3),k3_enumset1(X1,X1,X0,X2,X0)))) )),
% 1.72/0.59    inference(backward_demodulation,[],[f68,f71])).
% 1.72/0.59  fof(f68,plain,(
% 1.72/0.59    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k2_tarski(X0,X1),k4_xboole_0(k2_tarski(X2,X3),k2_tarski(X0,X1))) = k5_xboole_0(k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))),k4_xboole_0(k2_tarski(X3,X3),k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0)))))) )),
% 1.72/0.59    inference(definition_unfolding,[],[f44,f63,f50,f62,f43])).
% 1.72/0.59  fof(f44,plain,(
% 1.72/0.59    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))) )),
% 1.72/0.59    inference(cnf_transformation,[],[f13])).
% 1.72/0.59  fof(f13,axiom,(
% 1.72/0.59    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).
% 1.72/0.59  fof(f276,plain,(
% 1.72/0.59    ( ! [X14,X12,X13] : (r2_hidden(X14,k3_enumset1(X13,X13,X13,X12,X14))) )),
% 1.72/0.59    inference(superposition,[],[f129,f169])).
% 1.72/0.59  fof(f169,plain,(
% 1.72/0.59    ( ! [X4,X2,X3] : (k3_enumset1(X2,X2,X3,X4,X3) = k3_enumset1(X3,X3,X3,X2,X4)) )),
% 1.72/0.59    inference(superposition,[],[f89,f71])).
% 1.72/0.59  fof(f89,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.72/0.59    inference(forward_demodulation,[],[f72,f71])).
% 1.72/0.59  fof(f72,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) )),
% 1.72/0.59    inference(definition_unfolding,[],[f52,f62,f63])).
% 1.72/0.59  fof(f52,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f16])).
% 1.72/0.59  fof(f16,axiom,(
% 1.72/0.59    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.72/0.59  fof(f129,plain,(
% 1.72/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,k3_enumset1(X1,X1,X2,X0,X2))) )),
% 1.72/0.59    inference(unit_resulting_resolution,[],[f84,f93])).
% 1.72/0.59  fof(f93,plain,(
% 1.72/0.59    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k3_enumset1(X1,X1,X0,X2,X0)) | ~sP6(X4,X2,X1,X0)) )),
% 1.72/0.59    inference(forward_demodulation,[],[f83,f71])).
% 1.72/0.59  fof(f83,plain,(
% 1.72/0.59    ( ! [X4,X2,X0,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))))) )),
% 1.72/0.59    inference(equality_resolution,[],[f76])).
% 1.72/0.59  fof(f76,plain,(
% 1.72/0.59    ( ! [X4,X2,X0,X3,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,X3) | k5_xboole_0(k2_tarski(X1,X0),k4_xboole_0(k2_tarski(X2,X0),k2_tarski(X1,X0))) != X3) )),
% 1.72/0.59    inference(definition_unfolding,[],[f57,f62])).
% 1.72/0.59  fof(f57,plain,(
% 1.72/0.59    ( ! [X4,X2,X0,X3,X1] : (~sP6(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.72/0.59    inference(cnf_transformation,[],[f27])).
% 1.72/0.59  fof(f27,plain,(
% 1.72/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.72/0.59    inference(ennf_transformation,[],[f9])).
% 1.72/0.59  fof(f9,axiom,(
% 1.72/0.59    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.72/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 1.72/0.59  fof(f84,plain,(
% 1.72/0.59    ( ! [X4,X0,X1] : (sP6(X4,X4,X1,X0)) )),
% 1.72/0.59    inference(equality_resolution,[],[f55])).
% 1.72/0.59  fof(f55,plain,(
% 1.72/0.59    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP6(X4,X2,X1,X0)) )),
% 1.72/0.59    inference(cnf_transformation,[],[f27])).
% 1.72/0.59  % SZS output end Proof for theBenchmark
% 1.72/0.59  % (30629)------------------------------
% 1.72/0.59  % (30629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.59  % (30629)Termination reason: Refutation
% 1.72/0.59  
% 1.72/0.59  % (30629)Memory used [KB]: 2174
% 1.72/0.59  % (30629)Time elapsed: 0.158 s
% 1.72/0.59  % (30629)------------------------------
% 1.72/0.59  % (30629)------------------------------
% 1.72/0.59  % (30609)Success in time 0.221 s
%------------------------------------------------------------------------------

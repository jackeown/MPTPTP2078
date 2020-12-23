%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:58 EST 2020

% Result     : Theorem 38.06s
% Output     : Refutation 38.06s
% Verified   : 
% Statistics : Number of formulae       :   99 (2515 expanded)
%              Number of leaves         :   14 ( 818 expanded)
%              Depth                    :   34
%              Number of atoms          :  115 (2679 expanded)
%              Number of equality atoms :  100 (2662 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93873,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56152,f60130,f93857])).

fof(f93857,plain,(
    spl3_42 ),
    inference(avatar_contradiction_clause,[],[f93856])).

fof(f93856,plain,
    ( $false
    | spl3_42 ),
    inference(subsumption_resolution,[],[f93855,f32111])).

fof(f32111,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0))
    | spl3_42 ),
    inference(avatar_component_clause,[],[f32109])).

fof(f32109,plain,
    ( spl3_42
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f93855,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f93704,f35172])).

fof(f35172,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f58,f35164])).

fof(f35164,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f35150,f31522])).

fof(f31522,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(superposition,[],[f1551,f34])).

fof(f34,plain,(
    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0) ),
    inference(superposition,[],[f20,f32])).

fof(f32,plain,(
    k1_xboole_0 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2) ),
    inference(definition_unfolding,[],[f18,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f18,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)
   => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f1551,plain,(
    ! [X46] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X46),k4_xboole_0(k1_xboole_0,X46)) ),
    inference(superposition,[],[f56,f32])).

fof(f56,plain,(
    ! [X4,X5,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(k2_xboole_0(X3,X5),X4)) ),
    inference(superposition,[],[f20,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f35150,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))
    | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f23,f35117])).

fof(f35117,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f1658,f27908])).

fof(f27908,plain,(
    ! [X4,X2,X0,X3,X1] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X1),k4_enumset1(X0,X0,X1,X2,X3,X4))),k1_xboole_0) ),
    inference(backward_demodulation,[],[f4187,f2054])).

fof(f2054,plain,(
    ! [X14,X19,X17,X15,X20,X18,X16] : k4_xboole_0(k2_xboole_0(k1_tarski(X14),X20),k4_enumset1(X14,X15,X16,X17,X18,X19)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X20,k4_enumset1(X14,X15,X16,X17,X18,X19))) ),
    inference(superposition,[],[f25,f367])).

fof(f367,plain,(
    ! [X14,X12,X17,X15,X13,X16] : k1_xboole_0 = k4_xboole_0(k1_tarski(X12),k4_enumset1(X12,X13,X14,X15,X16,X17)) ),
    inference(superposition,[],[f20,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X1,X2,X3,X4,X5)) ),
    inference(definition_unfolding,[],[f28,f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f28,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f4187,plain,(
    ! [X4,X2,X0,X3,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_enumset1(X0,X0,X1,X2,X3,X4)),k1_xboole_0) ),
    inference(superposition,[],[f56,f722])).

fof(f722,plain,(
    ! [X28,X26,X29,X27,X25] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X25),k1_tarski(X26)),k1_tarski(X27)),k4_enumset1(X25,X25,X26,X27,X28,X29)) ),
    inference(superposition,[],[f20,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4))) ),
    inference(definition_unfolding,[],[f27,f26,f30,f21])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)) ),
    inference(definition_unfolding,[],[f24,f21])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).

fof(f27,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).

fof(f1658,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0)),k1_xboole_0) ),
    inference(superposition,[],[f1563,f56])).

fof(f1563,plain,(
    ! [X69] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X69),k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X69)) ),
    inference(superposition,[],[f56,f58])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f58,plain,(
    k2_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f57,f32])).

fof(f57,plain,(
    ! [X3] : k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X3),k1_xboole_0) = k2_xboole_0(k1_xboole_0,X3) ),
    inference(forward_demodulation,[],[f52,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f52,plain,(
    ! [X3] : k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X3),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,k1_xboole_0)) ),
    inference(superposition,[],[f25,f34])).

fof(f93704,plain,(
    k2_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0)) ),
    inference(superposition,[],[f2605,f80947])).

fof(f80947,plain,(
    ! [X3] : k2_xboole_0(k1_xboole_0,X3) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0))) ),
    inference(forward_demodulation,[],[f80865,f56153])).

fof(f56153,plain,(
    ! [X8] : k2_xboole_0(k1_xboole_0,X8) = k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0),X8),k1_xboole_0) ),
    inference(forward_demodulation,[],[f56117,f22])).

fof(f56117,plain,(
    ! [X8] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0),X8),k1_xboole_0) ),
    inference(superposition,[],[f25,f41706])).

fof(f41706,plain,(
    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f41412,f32])).

fof(f41412,plain,(
    ! [X30,X28,X29] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k2_xboole_0(X28,X29),k1_xboole_0),k2_xboole_0(k2_xboole_0(X28,X29),X30)) ),
    inference(backward_demodulation,[],[f2598,f39018])).

fof(f39018,plain,(
    ! [X2,X0,X1] : k1_xboole_0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) ),
    inference(backward_demodulation,[],[f37249,f38766])).

fof(f38766,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f35713,f367])).

fof(f35713,plain,(
    ! [X4,X2,X0,X3,X1] : k1_xboole_0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X0),k4_enumset1(X1,X1,X0,X2,X3,X4))) ),
    inference(superposition,[],[f35251,f27908])).

fof(f35251,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f35211,f22])).

fof(f35211,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f51,f35172])).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f25,f20])).

fof(f37249,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) ),
    inference(forward_demodulation,[],[f37179,f22])).

fof(f37179,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2))) ),
    inference(superposition,[],[f37178,f1588])).

fof(f1588,plain,(
    ! [X21,X19,X20] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X19,k2_xboole_0(k2_xboole_0(X19,X20),X21)),k1_xboole_0) ),
    inference(superposition,[],[f56,f20])).

fof(f37178,plain,(
    ! [X15] : k2_xboole_0(k1_xboole_0,X15) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X15,k1_xboole_0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f35221,f35251])).

fof(f35221,plain,(
    ! [X15] : k4_xboole_0(k2_xboole_0(k1_xboole_0,X15),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X15,k1_xboole_0),k1_xboole_0)) ),
    inference(superposition,[],[f2583,f35172])).

fof(f2583,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X2))) ),
    inference(superposition,[],[f51,f22])).

fof(f2598,plain,(
    ! [X30,X28,X29] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X28,k2_xboole_0(k2_xboole_0(X28,X29),X30))) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X28,X29),k1_xboole_0),k2_xboole_0(k2_xboole_0(X28,X29),X30)) ),
    inference(superposition,[],[f51,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[],[f22,f20])).

fof(f80865,plain,(
    ! [X3] : k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0),X3),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0))) ),
    inference(superposition,[],[f56153,f22])).

fof(f2605,plain,(
    ! [X48] : k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X48))) = k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X48)) ),
    inference(superposition,[],[f51,f32])).

fof(f60130,plain,(
    ~ spl3_41 ),
    inference(avatar_contradiction_clause,[],[f60129])).

fof(f60129,plain,
    ( $false
    | ~ spl3_41 ),
    inference(trivial_inequality_removal,[],[f60091])).

fof(f60091,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl3_41 ),
    inference(superposition,[],[f58900,f59900])).

fof(f59900,plain,
    ( ! [X6,X5] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_enumset1(sK0,sK0,sK1,sK0,X5,X6))
    | ~ spl3_41 ),
    inference(superposition,[],[f4185,f32107])).

fof(f32107,plain,
    ( k1_xboole_0 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f32105])).

fof(f32105,plain,
    ( spl3_41
  <=> k1_xboole_0 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f4185,plain,(
    ! [X2,X0,X3,X1] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_xboole_0),k4_enumset1(X0,X0,X1,X0,X2,X3)) ),
    inference(superposition,[],[f722,f35])).

fof(f58900,plain,(
    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k4_enumset1(sK0,sK0,sK1,sK0,sK0,sK1)) ),
    inference(subsumption_resolution,[],[f58876,f365])).

fof(f365,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k1_xboole_0 != k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(superposition,[],[f19,f31])).

fof(f19,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f58876,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k4_enumset1(sK0,sK0,sK1,sK0,sK0,sK1))
    | k1_xboole_0 = k4_enumset1(sK0,sK0,sK1,sK0,sK0,sK1) ),
    inference(superposition,[],[f23,f58839])).

fof(f58839,plain,(
    k1_xboole_0 = k4_xboole_0(k4_enumset1(sK0,sK0,sK1,sK0,sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f58747,f713])).

fof(f713,plain,(
    ! [X6,X7,X5] : k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X5),k1_tarski(X6)),k1_tarski(X7)),k1_xboole_0) = k4_enumset1(X5,X5,X6,X7,X5,X6) ),
    inference(superposition,[],[f33,f35])).

fof(f58747,plain,(
    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0)),k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f43447,f32])).

fof(f43447,plain,(
    ! [X21,X19,X20] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(X19,X20),X19),k1_xboole_0),k2_xboole_0(k2_xboole_0(X19,X20),X21)) ),
    inference(forward_demodulation,[],[f43367,f38766])).

fof(f43367,plain,(
    ! [X21,X19,X20] : k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(X19,X20),X19),k1_xboole_0),k2_xboole_0(k2_xboole_0(X19,X20),X21)) ),
    inference(superposition,[],[f3233,f41793])).

fof(f41793,plain,(
    ! [X47,X45,X46] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k2_xboole_0(X45,X46),X45),k2_xboole_0(k2_xboole_0(X45,X46),X47)) ),
    inference(backward_demodulation,[],[f2604,f41710])).

fof(f41710,plain,(
    ! [X6,X7,X5] : k1_xboole_0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X5,X6),X7))) ),
    inference(superposition,[],[f41412,f51])).

fof(f2604,plain,(
    ! [X47,X45,X46] : k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X45,X46),X47))) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X45,X46),X45),k2_xboole_0(k2_xboole_0(X45,X46),X47)) ),
    inference(superposition,[],[f51,f35])).

fof(f3233,plain,(
    ! [X33,X34,X32] : k2_xboole_0(k4_xboole_0(k2_xboole_0(X32,X33),k2_xboole_0(X32,X34)),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X32,X33),k1_xboole_0),k2_xboole_0(X32,X34)) ),
    inference(superposition,[],[f53,f35])).

fof(f53,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X2,k2_xboole_0(X0,X1)),k1_xboole_0) ),
    inference(superposition,[],[f25,f20])).

fof(f56152,plain,
    ( spl3_41
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f56116,f32109,f32105])).

fof(f56116,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0))
    | k1_xboole_0 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0) ),
    inference(superposition,[],[f23,f41706])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:12:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (31791)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (31807)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.51  % (31788)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (31787)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (31789)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (31798)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (31799)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (31804)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.52  % (31785)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (31805)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (31796)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (31800)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (31796)Refutation not found, incomplete strategy% (31796)------------------------------
% 0.21/0.53  % (31796)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31796)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31796)Memory used [KB]: 10618
% 0.21/0.53  % (31796)Time elapsed: 0.124 s
% 0.21/0.53  % (31796)------------------------------
% 0.21/0.53  % (31796)------------------------------
% 0.21/0.53  % (31797)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (31808)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % (31800)Refutation not found, incomplete strategy% (31800)------------------------------
% 0.21/0.53  % (31800)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (31800)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (31800)Memory used [KB]: 6140
% 0.21/0.53  % (31800)Time elapsed: 0.003 s
% 0.21/0.53  % (31800)------------------------------
% 0.21/0.53  % (31800)------------------------------
% 0.21/0.53  % (31812)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (31802)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (31811)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (31790)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (31792)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (31813)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (31786)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (31795)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.55  % (31795)Refutation not found, incomplete strategy% (31795)------------------------------
% 0.21/0.55  % (31795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31795)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (31795)Memory used [KB]: 10618
% 0.21/0.55  % (31795)Time elapsed: 0.140 s
% 0.21/0.55  % (31795)------------------------------
% 0.21/0.55  % (31795)------------------------------
% 0.21/0.55  % (31803)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.55  % (31793)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.55  % (31809)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.55  % (31794)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.55  % (31814)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.56  % (31802)Refutation not found, incomplete strategy% (31802)------------------------------
% 1.45/0.56  % (31802)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (31802)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (31802)Memory used [KB]: 10618
% 1.45/0.56  % (31802)Time elapsed: 0.148 s
% 1.45/0.56  % (31802)------------------------------
% 1.45/0.56  % (31802)------------------------------
% 1.45/0.56  % (31810)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.45/0.56  % (31806)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.56  % (31801)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 2.22/0.69  % (31825)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.22/0.69  % (31827)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.22/0.69  % (31828)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.67/0.73  % (31829)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.95/0.82  % (31790)Time limit reached!
% 2.95/0.82  % (31790)------------------------------
% 2.95/0.82  % (31790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.95/0.82  % (31790)Termination reason: Time limit
% 2.95/0.82  % (31790)Termination phase: Saturation
% 2.95/0.82  
% 2.95/0.82  % (31790)Memory used [KB]: 9722
% 2.95/0.82  % (31790)Time elapsed: 0.419 s
% 2.95/0.82  % (31790)------------------------------
% 2.95/0.82  % (31790)------------------------------
% 3.63/0.92  % (31797)Time limit reached!
% 3.63/0.92  % (31797)------------------------------
% 3.63/0.92  % (31797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.63/0.92  % (31797)Termination reason: Time limit
% 3.63/0.92  % (31797)Termination phase: Saturation
% 3.63/0.92  
% 3.63/0.92  % (31797)Memory used [KB]: 11641
% 3.63/0.92  % (31797)Time elapsed: 0.515 s
% 3.63/0.92  % (31797)------------------------------
% 3.63/0.92  % (31797)------------------------------
% 4.06/0.93  % (31786)Time limit reached!
% 4.06/0.93  % (31786)------------------------------
% 4.06/0.93  % (31786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.06/0.93  % (31786)Termination reason: Time limit
% 4.06/0.93  
% 4.06/0.93  % (31786)Memory used [KB]: 9594
% 4.06/0.93  % (31786)Time elapsed: 0.515 s
% 4.06/0.93  % (31786)------------------------------
% 4.06/0.93  % (31786)------------------------------
% 4.06/0.95  % (31785)Time limit reached!
% 4.06/0.95  % (31785)------------------------------
% 4.06/0.95  % (31785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.06/0.95  % (31785)Termination reason: Time limit
% 4.06/0.95  
% 4.06/0.95  % (31785)Memory used [KB]: 7547
% 4.06/0.95  % (31785)Time elapsed: 0.527 s
% 4.06/0.95  % (31785)------------------------------
% 4.06/0.95  % (31785)------------------------------
% 4.28/0.96  % (31830)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.28/1.02  % (31829)Time limit reached!
% 4.28/1.02  % (31829)------------------------------
% 4.28/1.02  % (31829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/1.02  % (31829)Termination reason: Time limit
% 4.28/1.02  
% 4.28/1.02  % (31829)Memory used [KB]: 7164
% 4.28/1.02  % (31829)Time elapsed: 0.434 s
% 4.28/1.02  % (31829)------------------------------
% 4.28/1.02  % (31829)------------------------------
% 4.80/1.04  % (31813)Time limit reached!
% 4.80/1.04  % (31813)------------------------------
% 4.80/1.04  % (31813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.80/1.04  % (31813)Termination reason: Time limit
% 4.80/1.04  
% 4.80/1.04  % (31813)Memory used [KB]: 9850
% 4.80/1.04  % (31813)Time elapsed: 0.615 s
% 4.80/1.04  % (31813)------------------------------
% 4.80/1.04  % (31813)------------------------------
% 4.80/1.04  % (31801)Time limit reached!
% 4.80/1.04  % (31801)------------------------------
% 4.80/1.04  % (31801)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.80/1.04  % (31801)Termination reason: Time limit
% 4.80/1.04  % (31801)Termination phase: Saturation
% 4.80/1.04  
% 4.80/1.04  % (31801)Memory used [KB]: 17014
% 4.80/1.04  % (31801)Time elapsed: 0.600 s
% 4.80/1.04  % (31801)------------------------------
% 4.80/1.04  % (31801)------------------------------
% 4.80/1.06  % (31831)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 4.80/1.06  % (31792)Time limit reached!
% 4.80/1.06  % (31792)------------------------------
% 4.80/1.06  % (31792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.80/1.06  % (31792)Termination reason: Time limit
% 4.80/1.06  
% 4.80/1.06  % (31792)Memory used [KB]: 10234
% 4.80/1.06  % (31792)Time elapsed: 0.621 s
% 4.80/1.06  % (31792)------------------------------
% 4.80/1.06  % (31792)------------------------------
% 4.80/1.07  % (31832)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 5.60/1.08  % (31833)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.14/1.17  % (31835)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 6.14/1.17  % (31836)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 6.38/1.19  % (31834)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.75/1.23  % (31806)Time limit reached!
% 6.75/1.23  % (31806)------------------------------
% 6.75/1.23  % (31806)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.75/1.23  % (31806)Termination reason: Time limit
% 6.75/1.23  
% 6.75/1.23  % (31806)Memory used [KB]: 10106
% 6.75/1.23  % (31806)Time elapsed: 0.821 s
% 6.75/1.23  % (31806)------------------------------
% 6.75/1.23  % (31806)------------------------------
% 6.75/1.23  % (31837)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 6.93/1.26  % (31830)Time limit reached!
% 6.93/1.26  % (31830)------------------------------
% 6.93/1.26  % (31830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.93/1.26  % (31830)Termination reason: Time limit
% 6.93/1.26  
% 6.93/1.26  % (31830)Memory used [KB]: 14456
% 6.93/1.26  % (31830)Time elapsed: 0.420 s
% 6.93/1.26  % (31830)------------------------------
% 6.93/1.26  % (31830)------------------------------
% 7.46/1.33  % (31838)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 7.86/1.40  % (31839)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 7.86/1.41  % (31787)Time limit reached!
% 7.86/1.41  % (31787)------------------------------
% 7.86/1.41  % (31787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.86/1.41  % (31787)Termination reason: Time limit
% 7.86/1.41  % (31787)Termination phase: Saturation
% 7.86/1.41  
% 7.86/1.41  % (31787)Memory used [KB]: 21108
% 7.86/1.41  % (31787)Time elapsed: 1.0000 s
% 7.86/1.41  % (31787)------------------------------
% 7.86/1.41  % (31787)------------------------------
% 9.20/1.58  % (31840)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 9.20/1.63  % (31807)Time limit reached!
% 9.20/1.63  % (31807)------------------------------
% 9.20/1.63  % (31807)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.20/1.63  % (31807)Termination reason: Time limit
% 9.20/1.63  
% 9.20/1.63  % (31807)Memory used [KB]: 22899
% 9.20/1.63  % (31807)Time elapsed: 1.217 s
% 9.20/1.63  % (31807)------------------------------
% 9.20/1.63  % (31807)------------------------------
% 10.40/1.73  % (31809)Time limit reached!
% 10.40/1.73  % (31809)------------------------------
% 10.40/1.73  % (31809)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.40/1.74  % (31809)Termination reason: Time limit
% 10.40/1.74  % (31809)Termination phase: Saturation
% 10.40/1.74  
% 10.40/1.74  % (31809)Memory used [KB]: 19957
% 10.40/1.74  % (31809)Time elapsed: 1.300 s
% 10.40/1.74  % (31809)------------------------------
% 10.40/1.74  % (31809)------------------------------
% 10.40/1.75  % (31838)Time limit reached!
% 10.40/1.75  % (31838)------------------------------
% 10.40/1.75  % (31838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.40/1.75  % (31838)Termination reason: Time limit
% 10.40/1.75  % (31838)Termination phase: Saturation
% 10.40/1.75  
% 10.40/1.75  % (31838)Memory used [KB]: 4733
% 10.40/1.75  % (31838)Time elapsed: 0.500 s
% 10.40/1.75  % (31838)------------------------------
% 10.40/1.75  % (31838)------------------------------
% 11.04/1.77  % (31841)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.04/1.77  % (31811)Time limit reached!
% 11.04/1.77  % (31811)------------------------------
% 11.04/1.77  % (31811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.04/1.77  % (31811)Termination reason: Time limit
% 11.04/1.77  
% 11.04/1.77  % (31811)Memory used [KB]: 15735
% 11.04/1.77  % (31811)Time elapsed: 1.371 s
% 11.04/1.77  % (31811)------------------------------
% 11.04/1.77  % (31811)------------------------------
% 11.60/1.85  % (31842)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.60/1.88  % (31843)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 11.60/1.92  % (31789)Time limit reached!
% 11.60/1.92  % (31789)------------------------------
% 11.60/1.92  % (31789)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.60/1.92  % (31789)Termination reason: Time limit
% 11.60/1.92  
% 11.60/1.92  % (31789)Memory used [KB]: 13688
% 11.60/1.92  % (31789)Time elapsed: 1.509 s
% 11.60/1.92  % (31789)------------------------------
% 11.60/1.92  % (31789)------------------------------
% 12.14/1.92  % (31812)Time limit reached!
% 12.14/1.92  % (31812)------------------------------
% 12.14/1.92  % (31812)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.14/1.92  % (31812)Termination reason: Time limit
% 12.14/1.92  % (31812)Termination phase: Saturation
% 12.14/1.92  
% 12.14/1.92  % (31812)Memory used [KB]: 24178
% 12.14/1.92  % (31812)Time elapsed: 1.500 s
% 12.14/1.92  % (31812)------------------------------
% 12.14/1.92  % (31812)------------------------------
% 12.14/1.93  % (31844)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 12.97/2.06  % (31846)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 12.97/2.08  % (31845)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 14.11/2.17  % (31842)Time limit reached!
% 14.11/2.17  % (31842)------------------------------
% 14.11/2.17  % (31842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.11/2.17  % (31842)Termination reason: Time limit
% 14.11/2.17  % (31842)Termination phase: Saturation
% 14.11/2.17  
% 14.11/2.17  % (31842)Memory used [KB]: 3582
% 14.11/2.17  % (31842)Time elapsed: 0.400 s
% 14.11/2.17  % (31842)------------------------------
% 14.11/2.17  % (31842)------------------------------
% 14.11/2.19  % (31832)Time limit reached!
% 14.11/2.19  % (31832)------------------------------
% 14.11/2.19  % (31832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.11/2.19  % (31832)Termination reason: Time limit
% 14.11/2.19  % (31832)Termination phase: Saturation
% 14.11/2.19  
% 14.11/2.19  % (31832)Memory used [KB]: 18038
% 14.11/2.19  % (31832)Time elapsed: 1.200 s
% 14.11/2.19  % (31832)------------------------------
% 14.11/2.19  % (31832)------------------------------
% 14.75/2.25  % (31799)Time limit reached!
% 14.75/2.25  % (31799)------------------------------
% 14.75/2.25  % (31799)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.75/2.25  % (31799)Termination reason: Time limit
% 14.75/2.25  % (31799)Termination phase: Saturation
% 14.75/2.25  
% 14.75/2.25  % (31799)Memory used [KB]: 24050
% 14.75/2.25  % (31799)Time elapsed: 1.800 s
% 14.75/2.25  % (31799)------------------------------
% 14.75/2.25  % (31799)------------------------------
% 14.75/2.25  % (31847)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 14.75/2.29  % (31828)Time limit reached!
% 14.75/2.29  % (31828)------------------------------
% 14.75/2.29  % (31828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.75/2.29  % (31828)Termination reason: Time limit
% 14.75/2.29  % (31828)Termination phase: Saturation
% 14.75/2.29  
% 14.75/2.29  % (31828)Memory used [KB]: 25713
% 14.75/2.29  % (31828)Time elapsed: 1.700 s
% 14.75/2.29  % (31828)------------------------------
% 14.75/2.29  % (31828)------------------------------
% 14.75/2.33  % (31848)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 14.75/2.35  % (31845)Time limit reached!
% 14.75/2.35  % (31845)------------------------------
% 14.75/2.35  % (31845)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.75/2.35  % (31845)Termination reason: Time limit
% 14.75/2.35  
% 14.75/2.35  % (31845)Memory used [KB]: 2686
% 14.75/2.35  % (31845)Time elapsed: 0.402 s
% 14.75/2.35  % (31845)------------------------------
% 14.75/2.35  % (31845)------------------------------
% 14.75/2.35  % (31849)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 16.03/2.42  % (31803)Time limit reached!
% 16.03/2.42  % (31803)------------------------------
% 16.03/2.42  % (31803)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.03/2.42  % (31803)Termination reason: Time limit
% 16.03/2.42  % (31803)Termination phase: Saturation
% 16.03/2.42  
% 16.03/2.42  % (31803)Memory used [KB]: 29167
% 16.03/2.42  % (31803)Time elapsed: 2.0000 s
% 16.03/2.42  % (31803)------------------------------
% 16.03/2.42  % (31803)------------------------------
% 16.03/2.42  % (31791)Time limit reached!
% 16.03/2.42  % (31791)------------------------------
% 16.03/2.42  % (31791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.03/2.42  % (31791)Termination reason: Time limit
% 16.03/2.42  % (31791)Termination phase: Saturation
% 16.03/2.42  
% 16.03/2.42  % (31791)Memory used [KB]: 36076
% 16.03/2.42  % (31791)Time elapsed: 2.0000 s
% 16.03/2.42  % (31791)------------------------------
% 16.03/2.42  % (31791)------------------------------
% 16.03/2.42  % (31850)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 16.26/2.48  % (31849)Refutation not found, incomplete strategy% (31849)------------------------------
% 16.26/2.48  % (31849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 16.26/2.48  % (31849)Termination reason: Refutation not found, incomplete strategy
% 16.26/2.48  
% 16.26/2.48  % (31849)Memory used [KB]: 6140
% 16.26/2.48  % (31849)Time elapsed: 0.181 s
% 16.26/2.48  % (31849)------------------------------
% 16.26/2.48  % (31849)------------------------------
% 16.26/2.49  % (31851)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 16.85/2.56  % (31853)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 16.85/2.57  % (31852)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 18.65/2.73  % (31850)Time limit reached!
% 18.65/2.73  % (31850)------------------------------
% 18.65/2.73  % (31850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.65/2.73  % (31850)Termination reason: Time limit
% 18.65/2.73  
% 18.65/2.73  % (31850)Memory used [KB]: 10490
% 18.65/2.73  % (31850)Time elapsed: 0.406 s
% 18.65/2.73  % (31850)------------------------------
% 18.65/2.73  % (31850)------------------------------
% 18.93/2.80  % (31834)Time limit reached!
% 18.93/2.80  % (31834)------------------------------
% 18.93/2.80  % (31834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 18.93/2.80  % (31834)Termination reason: Time limit
% 18.93/2.80  
% 18.93/2.80  % (31834)Memory used [KB]: 17014
% 18.93/2.80  % (31834)Time elapsed: 1.727 s
% 18.93/2.80  % (31834)------------------------------
% 18.93/2.80  % (31834)------------------------------
% 19.62/2.84  % (31841)Time limit reached!
% 19.62/2.84  % (31841)------------------------------
% 19.62/2.84  % (31841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.62/2.84  % (31841)Termination reason: Time limit
% 19.62/2.84  % (31841)Termination phase: Saturation
% 19.62/2.84  
% 19.62/2.84  % (31841)Memory used [KB]: 18166
% 19.62/2.84  % (31841)Time elapsed: 1.200 s
% 19.62/2.84  % (31841)------------------------------
% 19.62/2.84  % (31841)------------------------------
% 19.62/2.85  % (31852)Time limit reached!
% 19.62/2.85  % (31852)------------------------------
% 19.62/2.85  % (31852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.62/2.85  % (31852)Termination reason: Time limit
% 19.62/2.85  % (31852)Termination phase: Saturation
% 19.62/2.85  
% 19.62/2.85  % (31852)Memory used [KB]: 10234
% 19.62/2.85  % (31852)Time elapsed: 0.400 s
% 19.62/2.85  % (31852)------------------------------
% 19.62/2.85  % (31852)------------------------------
% 20.97/3.01  % (31804)Time limit reached!
% 20.97/3.01  % (31804)------------------------------
% 20.97/3.01  % (31804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 20.97/3.01  % (31804)Termination reason: Time limit
% 20.97/3.01  
% 20.97/3.01  % (31804)Memory used [KB]: 45798
% 20.97/3.01  % (31804)Time elapsed: 2.608 s
% 20.97/3.01  % (31804)------------------------------
% 20.97/3.01  % (31804)------------------------------
% 22.05/3.14  % (31844)Time limit reached!
% 22.05/3.14  % (31844)------------------------------
% 22.05/3.14  % (31844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 22.05/3.14  % (31844)Termination reason: Time limit
% 22.05/3.14  
% 22.05/3.14  % (31844)Memory used [KB]: 19957
% 22.05/3.14  % (31844)Time elapsed: 1.316 s
% 22.05/3.14  % (31844)------------------------------
% 22.05/3.14  % (31844)------------------------------
% 23.83/3.41  % (31827)Time limit reached!
% 23.83/3.41  % (31827)------------------------------
% 23.83/3.41  % (31827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.83/3.41  % (31827)Termination reason: Time limit
% 23.83/3.41  % (31827)Termination phase: Saturation
% 23.83/3.41  
% 23.83/3.41  % (31827)Memory used [KB]: 34157
% 23.83/3.41  % (31827)Time elapsed: 2.800 s
% 23.83/3.41  % (31827)------------------------------
% 23.83/3.41  % (31827)------------------------------
% 23.83/3.41  % (31798)Time limit reached!
% 23.83/3.41  % (31798)------------------------------
% 23.83/3.41  % (31798)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.83/3.41  % (31798)Termination reason: Time limit
% 23.83/3.41  
% 23.83/3.41  % (31798)Memory used [KB]: 11385
% 23.83/3.41  % (31798)Time elapsed: 3.007 s
% 23.83/3.41  % (31798)------------------------------
% 23.83/3.41  % (31798)------------------------------
% 23.83/3.42  % (31793)Time limit reached!
% 23.83/3.42  % (31793)------------------------------
% 23.83/3.42  % (31793)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 23.83/3.43  % (31793)Termination reason: Time limit
% 23.83/3.43  
% 23.83/3.43  % (31793)Memory used [KB]: 28016
% 23.83/3.43  % (31793)Time elapsed: 2.999 s
% 23.83/3.43  % (31793)------------------------------
% 23.83/3.43  % (31793)------------------------------
% 31.00/4.33  % (31814)Time limit reached!
% 31.00/4.33  % (31814)------------------------------
% 31.00/4.33  % (31814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 31.00/4.33  % (31814)Termination reason: Time limit
% 31.00/4.33  
% 31.00/4.33  % (31814)Memory used [KB]: 44391
% 31.00/4.33  % (31814)Time elapsed: 3.907 s
% 31.00/4.33  % (31814)------------------------------
% 31.00/4.33  % (31814)------------------------------
% 36.38/4.93  % (31840)Time limit reached!
% 36.38/4.93  % (31840)------------------------------
% 36.38/4.93  % (31840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.38/4.93  % (31840)Termination reason: Time limit
% 36.38/4.93  % (31840)Termination phase: Saturation
% 36.38/4.93  
% 36.38/4.93  % (31840)Memory used [KB]: 61150
% 36.38/4.93  % (31840)Time elapsed: 3.500 s
% 36.38/4.93  % (31840)------------------------------
% 36.38/4.93  % (31840)------------------------------
% 36.82/5.02  % (31794)Time limit reached!
% 36.82/5.02  % (31794)------------------------------
% 36.82/5.02  % (31794)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.82/5.02  % (31794)Termination reason: Time limit
% 36.82/5.02  % (31794)Termination phase: Saturation
% 36.82/5.02  
% 36.82/5.02  % (31794)Memory used [KB]: 62173
% 36.82/5.02  % (31794)Time elapsed: 4.600 s
% 36.82/5.02  % (31794)------------------------------
% 36.82/5.02  % (31794)------------------------------
% 38.06/5.16  % (31788)Refutation found. Thanks to Tanya!
% 38.06/5.16  % SZS status Theorem for theBenchmark
% 38.06/5.16  % SZS output start Proof for theBenchmark
% 38.06/5.16  fof(f93873,plain,(
% 38.06/5.16    $false),
% 38.06/5.16    inference(avatar_sat_refutation,[],[f56152,f60130,f93857])).
% 38.06/5.16  fof(f93857,plain,(
% 38.06/5.16    spl3_42),
% 38.06/5.16    inference(avatar_contradiction_clause,[],[f93856])).
% 38.06/5.16  fof(f93856,plain,(
% 38.06/5.16    $false | spl3_42),
% 38.06/5.16    inference(subsumption_resolution,[],[f93855,f32111])).
% 38.06/5.16  fof(f32111,plain,(
% 38.06/5.16    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0)) | spl3_42),
% 38.06/5.16    inference(avatar_component_clause,[],[f32109])).
% 38.06/5.16  fof(f32109,plain,(
% 38.06/5.16    spl3_42 <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0))),
% 38.06/5.16    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 38.06/5.16  fof(f93855,plain,(
% 38.06/5.16    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0))),
% 38.06/5.16    inference(forward_demodulation,[],[f93704,f35172])).
% 38.06/5.16  fof(f35172,plain,(
% 38.06/5.16    k1_xboole_0 = k2_xboole_0(k1_xboole_0,sK2)),
% 38.06/5.16    inference(backward_demodulation,[],[f58,f35164])).
% 38.06/5.16  fof(f35164,plain,(
% 38.06/5.16    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 38.06/5.16    inference(subsumption_resolution,[],[f35150,f31522])).
% 38.06/5.16  fof(f31522,plain,(
% 38.06/5.16    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0))),
% 38.06/5.16    inference(superposition,[],[f1551,f34])).
% 38.06/5.16  fof(f34,plain,(
% 38.06/5.16    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0)),
% 38.06/5.16    inference(superposition,[],[f20,f32])).
% 38.06/5.16  fof(f32,plain,(
% 38.06/5.16    k1_xboole_0 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),sK2)),
% 38.06/5.16    inference(definition_unfolding,[],[f18,f21])).
% 38.06/5.16  fof(f21,plain,(
% 38.06/5.16    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 38.06/5.16    inference(cnf_transformation,[],[f6])).
% 38.06/5.16  fof(f6,axiom,(
% 38.06/5.16    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 38.06/5.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 38.06/5.16  fof(f18,plain,(
% 38.06/5.16    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 38.06/5.16    inference(cnf_transformation,[],[f17])).
% 38.06/5.16  fof(f17,plain,(
% 38.06/5.16    k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 38.06/5.16    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f16])).
% 38.06/5.16  fof(f16,plain,(
% 38.06/5.16    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2) => k1_xboole_0 = k2_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 38.06/5.16    introduced(choice_axiom,[])).
% 38.06/5.16  fof(f14,plain,(
% 38.06/5.16    ? [X0,X1,X2] : k1_xboole_0 = k2_xboole_0(k2_tarski(X0,X1),X2)),
% 38.06/5.16    inference(ennf_transformation,[],[f13])).
% 38.06/5.16  fof(f13,negated_conjecture,(
% 38.06/5.16    ~! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 38.06/5.16    inference(negated_conjecture,[],[f12])).
% 38.06/5.16  fof(f12,conjecture,(
% 38.06/5.16    ! [X0,X1,X2] : k1_xboole_0 != k2_xboole_0(k2_tarski(X0,X1),X2)),
% 38.06/5.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).
% 38.06/5.16  fof(f20,plain,(
% 38.06/5.16    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 38.06/5.16    inference(cnf_transformation,[],[f4])).
% 38.06/5.16  fof(f4,axiom,(
% 38.06/5.16    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 38.06/5.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 38.06/5.16  fof(f1551,plain,(
% 38.06/5.16    ( ! [X46] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X46),k4_xboole_0(k1_xboole_0,X46))) )),
% 38.06/5.16    inference(superposition,[],[f56,f32])).
% 38.06/5.16  fof(f56,plain,(
% 38.06/5.16    ( ! [X4,X5,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(k2_xboole_0(X3,X5),X4))) )),
% 38.06/5.16    inference(superposition,[],[f20,f25])).
% 38.06/5.16  fof(f25,plain,(
% 38.06/5.16    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 38.06/5.16    inference(cnf_transformation,[],[f3])).
% 38.06/5.16  fof(f3,axiom,(
% 38.06/5.16    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 38.06/5.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 38.06/5.16  fof(f35150,plain,(
% 38.06/5.16    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) | k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 38.06/5.16    inference(superposition,[],[f23,f35117])).
% 38.06/5.16  fof(f35117,plain,(
% 38.06/5.16    k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 38.06/5.16    inference(superposition,[],[f1658,f27908])).
% 38.06/5.16  fof(f27908,plain,(
% 38.06/5.16    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X1),k4_enumset1(X0,X0,X1,X2,X3,X4))),k1_xboole_0)) )),
% 38.06/5.16    inference(backward_demodulation,[],[f4187,f2054])).
% 38.06/5.16  fof(f2054,plain,(
% 38.06/5.16    ( ! [X14,X19,X17,X15,X20,X18,X16] : (k4_xboole_0(k2_xboole_0(k1_tarski(X14),X20),k4_enumset1(X14,X15,X16,X17,X18,X19)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X20,k4_enumset1(X14,X15,X16,X17,X18,X19)))) )),
% 38.06/5.16    inference(superposition,[],[f25,f367])).
% 38.06/5.16  fof(f367,plain,(
% 38.06/5.16    ( ! [X14,X12,X17,X15,X13,X16] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X12),k4_enumset1(X12,X13,X14,X15,X16,X17))) )),
% 38.06/5.16    inference(superposition,[],[f20,f31])).
% 38.06/5.16  fof(f31,plain,(
% 38.06/5.16    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X1,X2,X3,X4,X5))) )),
% 38.06/5.16    inference(definition_unfolding,[],[f28,f26])).
% 38.06/5.16  fof(f26,plain,(
% 38.06/5.16    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 38.06/5.16    inference(cnf_transformation,[],[f9])).
% 38.06/5.16  fof(f9,axiom,(
% 38.06/5.16    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 38.06/5.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 38.06/5.16  fof(f28,plain,(
% 38.06/5.16    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))) )),
% 38.06/5.16    inference(cnf_transformation,[],[f8])).
% 38.06/5.16  fof(f8,axiom,(
% 38.06/5.16    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5))),
% 38.06/5.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).
% 38.06/5.16  fof(f4187,plain,(
% 38.06/5.16    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k4_enumset1(X0,X0,X1,X2,X3,X4)),k1_xboole_0)) )),
% 38.06/5.16    inference(superposition,[],[f56,f722])).
% 38.06/5.16  fof(f722,plain,(
% 38.06/5.16    ( ! [X28,X26,X29,X27,X25] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X25),k1_tarski(X26)),k1_tarski(X27)),k4_enumset1(X25,X25,X26,X27,X28,X29))) )),
% 38.06/5.16    inference(superposition,[],[f20,f33])).
% 38.06/5.16  fof(f33,plain,(
% 38.06/5.16    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2)),k2_xboole_0(k1_tarski(X3),k1_tarski(X4)))) )),
% 38.06/5.16    inference(definition_unfolding,[],[f27,f26,f30,f21])).
% 38.06/5.16  fof(f30,plain,(
% 38.06/5.16    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_tarski(X2))) )),
% 38.06/5.16    inference(definition_unfolding,[],[f24,f21])).
% 38.06/5.16  fof(f24,plain,(
% 38.06/5.16    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 38.06/5.16    inference(cnf_transformation,[],[f7])).
% 38.06/5.16  fof(f7,axiom,(
% 38.06/5.16    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 38.06/5.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_enumset1)).
% 38.06/5.16  fof(f27,plain,(
% 38.06/5.16    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))) )),
% 38.06/5.16    inference(cnf_transformation,[],[f5])).
% 38.06/5.16  fof(f5,axiom,(
% 38.06/5.16    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_tarski(X3,X4))),
% 38.06/5.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l57_enumset1)).
% 38.06/5.16  fof(f1658,plain,(
% 38.06/5.16    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,k4_xboole_0(k2_xboole_0(k1_xboole_0,X1),k1_xboole_0)),k1_xboole_0)) )),
% 38.06/5.16    inference(superposition,[],[f1563,f56])).
% 38.06/5.16  fof(f1563,plain,(
% 38.06/5.16    ( ! [X69] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k1_xboole_0,X69),k4_xboole_0(k4_xboole_0(k1_xboole_0,k1_xboole_0),X69))) )),
% 38.06/5.16    inference(superposition,[],[f56,f58])).
% 38.06/5.16  fof(f23,plain,(
% 38.06/5.16    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 38.06/5.16    inference(cnf_transformation,[],[f15])).
% 38.06/5.16  fof(f15,plain,(
% 38.06/5.16    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 38.06/5.16    inference(ennf_transformation,[],[f1])).
% 38.06/5.16  fof(f1,axiom,(
% 38.06/5.16    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 38.06/5.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).
% 38.06/5.16  fof(f58,plain,(
% 38.06/5.16    k2_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 38.06/5.16    inference(superposition,[],[f57,f32])).
% 38.06/5.16  fof(f57,plain,(
% 38.06/5.16    ( ! [X3] : (k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X3),k1_xboole_0) = k2_xboole_0(k1_xboole_0,X3)) )),
% 38.06/5.16    inference(forward_demodulation,[],[f52,f22])).
% 38.06/5.16  fof(f22,plain,(
% 38.06/5.16    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 38.06/5.16    inference(cnf_transformation,[],[f2])).
% 38.06/5.16  fof(f2,axiom,(
% 38.06/5.16    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 38.06/5.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 38.06/5.16  fof(f52,plain,(
% 38.06/5.16    ( ! [X3] : (k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X3),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,k1_xboole_0))) )),
% 38.06/5.16    inference(superposition,[],[f25,f34])).
% 38.06/5.16  fof(f93704,plain,(
% 38.06/5.16    k2_xboole_0(k1_xboole_0,sK2) = k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0))),
% 38.06/5.16    inference(superposition,[],[f2605,f80947])).
% 38.06/5.16  fof(f80947,plain,(
% 38.06/5.16    ( ! [X3] : (k2_xboole_0(k1_xboole_0,X3) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0)))) )),
% 38.06/5.16    inference(forward_demodulation,[],[f80865,f56153])).
% 38.06/5.16  fof(f56153,plain,(
% 38.06/5.16    ( ! [X8] : (k2_xboole_0(k1_xboole_0,X8) = k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0),X8),k1_xboole_0)) )),
% 38.06/5.16    inference(forward_demodulation,[],[f56117,f22])).
% 38.06/5.16  fof(f56117,plain,(
% 38.06/5.16    ( ! [X8] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X8,k1_xboole_0)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0),X8),k1_xboole_0)) )),
% 38.06/5.16    inference(superposition,[],[f25,f41706])).
% 38.06/5.16  fof(f41706,plain,(
% 38.06/5.16    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0),k1_xboole_0)),
% 38.06/5.16    inference(superposition,[],[f41412,f32])).
% 38.06/5.16  fof(f41412,plain,(
% 38.06/5.16    ( ! [X30,X28,X29] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k2_xboole_0(X28,X29),k1_xboole_0),k2_xboole_0(k2_xboole_0(X28,X29),X30))) )),
% 38.06/5.16    inference(backward_demodulation,[],[f2598,f39018])).
% 38.06/5.16  fof(f39018,plain,(
% 38.06/5.16    ( ! [X2,X0,X1] : (k1_xboole_0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)))) )),
% 38.06/5.16    inference(backward_demodulation,[],[f37249,f38766])).
% 38.06/5.16  fof(f38766,plain,(
% 38.06/5.16    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 38.06/5.16    inference(superposition,[],[f35713,f367])).
% 38.06/5.16  fof(f35713,plain,(
% 38.06/5.16    ( ! [X4,X2,X0,X3,X1] : (k1_xboole_0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_tarski(X0),k4_enumset1(X1,X1,X0,X2,X3,X4)))) )),
% 38.06/5.16    inference(superposition,[],[f35251,f27908])).
% 38.06/5.16  fof(f35251,plain,(
% 38.06/5.16    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0)) )),
% 38.06/5.16    inference(forward_demodulation,[],[f35211,f22])).
% 38.06/5.16  fof(f35211,plain,(
% 38.06/5.16    ( ! [X0] : (k4_xboole_0(k2_xboole_0(k1_xboole_0,X0),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0))) )),
% 38.06/5.16    inference(superposition,[],[f51,f35172])).
% 38.06/5.16  fof(f51,plain,(
% 38.06/5.16    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X2),k2_xboole_0(X0,X1)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X2,k2_xboole_0(X0,X1)))) )),
% 38.06/5.16    inference(superposition,[],[f25,f20])).
% 38.06/5.16  fof(f37249,plain,(
% 38.06/5.16    ( ! [X2,X0,X1] : (k2_xboole_0(k1_xboole_0,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)))) )),
% 38.06/5.16    inference(forward_demodulation,[],[f37179,f22])).
% 38.06/5.16  fof(f37179,plain,(
% 38.06/5.16    ( ! [X2,X0,X1] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k1_xboole_0)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(X0,X1),X2)))) )),
% 38.06/5.16    inference(superposition,[],[f37178,f1588])).
% 38.06/5.16  fof(f1588,plain,(
% 38.06/5.16    ( ! [X21,X19,X20] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X19,k2_xboole_0(k2_xboole_0(X19,X20),X21)),k1_xboole_0)) )),
% 38.06/5.16    inference(superposition,[],[f56,f20])).
% 38.06/5.16  fof(f37178,plain,(
% 38.06/5.16    ( ! [X15] : (k2_xboole_0(k1_xboole_0,X15) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X15,k1_xboole_0),k1_xboole_0))) )),
% 38.06/5.16    inference(forward_demodulation,[],[f35221,f35251])).
% 38.06/5.16  fof(f35221,plain,(
% 38.06/5.16    ( ! [X15] : (k4_xboole_0(k2_xboole_0(k1_xboole_0,X15),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X15,k1_xboole_0),k1_xboole_0))) )),
% 38.06/5.16    inference(superposition,[],[f2583,f35172])).
% 38.06/5.16  fof(f2583,plain,(
% 38.06/5.16    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X1,X0),k2_xboole_0(X0,X2)))) )),
% 38.06/5.16    inference(superposition,[],[f51,f22])).
% 38.06/5.16  fof(f2598,plain,(
% 38.06/5.16    ( ! [X30,X28,X29] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X28,k2_xboole_0(k2_xboole_0(X28,X29),X30))) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X28,X29),k1_xboole_0),k2_xboole_0(k2_xboole_0(X28,X29),X30))) )),
% 38.06/5.16    inference(superposition,[],[f51,f35])).
% 38.06/5.16  fof(f35,plain,(
% 38.06/5.16    ( ! [X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) )),
% 38.06/5.16    inference(superposition,[],[f22,f20])).
% 38.06/5.16  fof(f80865,plain,(
% 38.06/5.16    ( ! [X3] : (k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0),X3),k1_xboole_0) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0)))) )),
% 38.06/5.16    inference(superposition,[],[f56153,f22])).
% 38.06/5.16  fof(f2605,plain,(
% 38.06/5.16    ( ! [X48] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X48))) = k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),X48))) )),
% 38.06/5.16    inference(superposition,[],[f51,f32])).
% 38.06/5.16  fof(f60130,plain,(
% 38.06/5.16    ~spl3_41),
% 38.06/5.16    inference(avatar_contradiction_clause,[],[f60129])).
% 38.06/5.16  fof(f60129,plain,(
% 38.06/5.16    $false | ~spl3_41),
% 38.06/5.16    inference(trivial_inequality_removal,[],[f60091])).
% 38.06/5.16  fof(f60091,plain,(
% 38.06/5.16    k1_xboole_0 != k1_xboole_0 | ~spl3_41),
% 38.06/5.16    inference(superposition,[],[f58900,f59900])).
% 38.06/5.16  fof(f59900,plain,(
% 38.06/5.16    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_enumset1(sK0,sK0,sK1,sK0,X5,X6))) ) | ~spl3_41),
% 38.06/5.16    inference(superposition,[],[f4185,f32107])).
% 38.06/5.16  fof(f32107,plain,(
% 38.06/5.16    k1_xboole_0 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0) | ~spl3_41),
% 38.06/5.16    inference(avatar_component_clause,[],[f32105])).
% 38.06/5.16  fof(f32105,plain,(
% 38.06/5.16    spl3_41 <=> k1_xboole_0 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0)),
% 38.06/5.16    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 38.06/5.16  fof(f4185,plain,(
% 38.06/5.16    ( ! [X2,X0,X3,X1] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)),k1_xboole_0),k4_enumset1(X0,X0,X1,X0,X2,X3))) )),
% 38.06/5.16    inference(superposition,[],[f722,f35])).
% 38.06/5.16  fof(f58900,plain,(
% 38.06/5.16    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k4_enumset1(sK0,sK0,sK1,sK0,sK0,sK1))),
% 38.06/5.16    inference(subsumption_resolution,[],[f58876,f365])).
% 38.06/5.16  fof(f365,plain,(
% 38.06/5.16    ( ! [X4,X2,X0,X5,X3,X1] : (k1_xboole_0 != k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 38.06/5.16    inference(superposition,[],[f19,f31])).
% 38.06/5.16  fof(f19,plain,(
% 38.06/5.16    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 38.06/5.16    inference(cnf_transformation,[],[f11])).
% 38.06/5.16  fof(f11,axiom,(
% 38.06/5.16    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 38.06/5.16    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 38.06/5.16  fof(f58876,plain,(
% 38.06/5.16    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k4_enumset1(sK0,sK0,sK1,sK0,sK0,sK1)) | k1_xboole_0 = k4_enumset1(sK0,sK0,sK1,sK0,sK0,sK1)),
% 38.06/5.16    inference(superposition,[],[f23,f58839])).
% 38.06/5.16  fof(f58839,plain,(
% 38.06/5.16    k1_xboole_0 = k4_xboole_0(k4_enumset1(sK0,sK0,sK1,sK0,sK0,sK1),k1_xboole_0)),
% 38.06/5.16    inference(forward_demodulation,[],[f58747,f713])).
% 38.06/5.16  fof(f713,plain,(
% 38.06/5.16    ( ! [X6,X7,X5] : (k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(X5),k1_tarski(X6)),k1_tarski(X7)),k1_xboole_0) = k4_enumset1(X5,X5,X6,X7,X5,X6)) )),
% 38.06/5.16    inference(superposition,[],[f33,f35])).
% 38.06/5.16  fof(f58747,plain,(
% 38.06/5.16    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_tarski(sK0)),k1_xboole_0),k1_xboole_0)),
% 38.06/5.16    inference(superposition,[],[f43447,f32])).
% 38.06/5.16  fof(f43447,plain,(
% 38.06/5.16    ( ! [X21,X19,X20] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(X19,X20),X19),k1_xboole_0),k2_xboole_0(k2_xboole_0(X19,X20),X21))) )),
% 38.06/5.16    inference(forward_demodulation,[],[f43367,f38766])).
% 38.06/5.16  fof(f43367,plain,(
% 38.06/5.16    ( ! [X21,X19,X20] : (k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k2_xboole_0(k2_xboole_0(k2_xboole_0(X19,X20),X19),k1_xboole_0),k2_xboole_0(k2_xboole_0(X19,X20),X21))) )),
% 38.06/5.16    inference(superposition,[],[f3233,f41793])).
% 38.06/5.16  fof(f41793,plain,(
% 38.06/5.16    ( ! [X47,X45,X46] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k2_xboole_0(X45,X46),X45),k2_xboole_0(k2_xboole_0(X45,X46),X47))) )),
% 38.06/5.16    inference(backward_demodulation,[],[f2604,f41710])).
% 38.06/5.16  fof(f41710,plain,(
% 38.06/5.16    ( ! [X6,X7,X5] : (k1_xboole_0 = k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X5,X6),X7)))) )),
% 38.06/5.16    inference(superposition,[],[f41412,f51])).
% 38.06/5.16  fof(f2604,plain,(
% 38.06/5.16    ( ! [X47,X45,X46] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(X45,X46),X47))) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X45,X46),X45),k2_xboole_0(k2_xboole_0(X45,X46),X47))) )),
% 38.06/5.16    inference(superposition,[],[f51,f35])).
% 38.06/5.16  fof(f3233,plain,(
% 38.06/5.16    ( ! [X33,X34,X32] : (k2_xboole_0(k4_xboole_0(k2_xboole_0(X32,X33),k2_xboole_0(X32,X34)),k1_xboole_0) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X32,X33),k1_xboole_0),k2_xboole_0(X32,X34))) )),
% 38.06/5.16    inference(superposition,[],[f53,f35])).
% 38.06/5.16  fof(f53,plain,(
% 38.06/5.16    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X2,X0),k2_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X2,k2_xboole_0(X0,X1)),k1_xboole_0)) )),
% 38.06/5.16    inference(superposition,[],[f25,f20])).
% 38.06/5.16  fof(f56152,plain,(
% 38.06/5.16    spl3_41 | ~spl3_42),
% 38.06/5.16    inference(avatar_split_clause,[],[f56116,f32109,f32105])).
% 38.06/5.16  fof(f56116,plain,(
% 38.06/5.16    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0)) | k1_xboole_0 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),k1_tarski(sK1)),k1_xboole_0)),
% 38.06/5.16    inference(superposition,[],[f23,f41706])).
% 38.06/5.16  % SZS output end Proof for theBenchmark
% 38.06/5.16  % (31788)------------------------------
% 38.06/5.16  % (31788)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 38.06/5.16  % (31788)Termination reason: Refutation
% 38.06/5.16  
% 38.06/5.16  % (31788)Memory used [KB]: 62301
% 38.06/5.16  % (31788)Time elapsed: 4.743 s
% 38.06/5.16  % (31788)------------------------------
% 38.06/5.16  % (31788)------------------------------
% 38.06/5.17  % (31784)Success in time 4.806 s
%------------------------------------------------------------------------------

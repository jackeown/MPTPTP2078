%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t54_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:00 EDT 2019

% Result     : Theorem 10.56s
% Output     : Refutation 10.56s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 115 expanded)
%              Number of leaves         :   11 (  39 expanded)
%              Depth                    :   13
%              Number of atoms          :   60 ( 127 expanded)
%              Number of equality atoms :   48 ( 111 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129269,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f7667,f44082,f129267])).

fof(f129267,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f129266])).

fof(f129266,plain,
    ( $false
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f129248,f66799])).

fof(f66799,plain,(
    ! [X187,X185,X188,X186,X184,X183] : k4_enumset1(X183,X184,X185,X186,X187,X188) = k2_xboole_0(k2_tarski(X187,X188),k2_enumset1(X183,X185,X184,X186)) ),
    inference(forward_demodulation,[],[f66656,f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t54_enumset1.p',l62_enumset1)).

fof(f66656,plain,(
    ! [X187,X185,X188,X186,X184,X183] : k2_xboole_0(k2_tarski(X187,X188),k2_enumset1(X183,X185,X184,X186)) = k2_xboole_0(k1_enumset1(X183,X184,X185),k1_enumset1(X186,X187,X188)) ),
    inference(superposition,[],[f202,f2085])).

fof(f2085,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X2,X1),k1_tarski(X3)) ),
    inference(superposition,[],[f26,f75])).

fof(f75,plain,(
    ! [X4,X5,X3] : k1_enumset1(X3,X4,X5) = k1_enumset1(X3,X5,X4) ),
    inference(superposition,[],[f28,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t54_enumset1.p',t42_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k1_tarski(X2),k2_tarski(X1,X0)) = k1_enumset1(X2,X0,X1) ),
    inference(superposition,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t54_enumset1.p',commutativity_k2_tarski)).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t54_enumset1.p',t46_enumset1)).

fof(f202,plain,(
    ! [X43,X41,X44,X42] : k2_xboole_0(X44,k1_enumset1(X41,X42,X43)) = k2_xboole_0(k2_tarski(X42,X43),k2_xboole_0(X44,k1_tarski(X41))) ),
    inference(superposition,[],[f40,f24])).

fof(f40,plain,(
    ! [X6,X7,X5] : k2_xboole_0(X5,k2_xboole_0(X6,X7)) = k2_xboole_0(X7,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f25,f22])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t54_enumset1.p',commutativity_k2_xboole_0)).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t54_enumset1.p',t4_xboole_1)).

fof(f129248,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK4,sK5),k2_enumset1(sK0,sK2,sK1,sK3))
    | ~ spl6_1 ),
    inference(superposition,[],[f7666,f9302])).

fof(f9302,plain,(
    ! [X227,X225,X228,X226,X224] : k2_xboole_0(X228,k2_enumset1(X224,X225,X226,X227)) = k2_xboole_0(k2_enumset1(X224,X226,X225,X227),X228) ),
    inference(forward_demodulation,[],[f9301,f2087])).

fof(f2087,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X4,X5,X6)) ),
    inference(superposition,[],[f26,f22])).

fof(f9301,plain,(
    ! [X227,X225,X228,X226,X224] : k2_xboole_0(k2_enumset1(X224,X226,X225,X227),X228) = k2_xboole_0(X228,k2_xboole_0(k1_tarski(X227),k1_enumset1(X224,X225,X226))) ),
    inference(forward_demodulation,[],[f9265,f2930])).

fof(f2930,plain,(
    ! [X134,X136,X135,X133,X137] : k2_xboole_0(k2_enumset1(X134,X135,X136,X133),X137) = k2_xboole_0(k2_enumset1(X134,X135,X136,X133),k2_xboole_0(k1_tarski(X133),X137)) ),
    inference(forward_demodulation,[],[f2758,f2093])).

fof(f2093,plain,(
    ! [X21,X19,X17,X20,X18] : k2_xboole_0(k2_enumset1(X17,X18,X19,X20),X21) = k2_xboole_0(k1_tarski(X20),k2_xboole_0(k1_enumset1(X17,X18,X19),X21)) ),
    inference(superposition,[],[f35,f26])).

fof(f35,plain,(
    ! [X4,X2,X3] : k2_xboole_0(X2,k2_xboole_0(X3,X4)) = k2_xboole_0(k2_xboole_0(X3,X2),X4) ),
    inference(superposition,[],[f25,f22])).

fof(f2758,plain,(
    ! [X134,X136,X135,X133,X137] : k2_xboole_0(k1_tarski(X133),k2_xboole_0(k1_enumset1(X134,X135,X136),X137)) = k2_xboole_0(k2_enumset1(X134,X135,X136,X133),k2_xboole_0(k1_tarski(X133),X137)) ),
    inference(superposition,[],[f118,f2087])).

fof(f118,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X8,k2_xboole_0(X9,X10)) = k2_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X8,X10)) ),
    inference(forward_demodulation,[],[f96,f25])).

fof(f96,plain,(
    ! [X10,X8,X9] : k2_xboole_0(k2_xboole_0(X8,X9),X10) = k2_xboole_0(k2_xboole_0(X8,X9),k2_xboole_0(X8,X10)) ),
    inference(superposition,[],[f35,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f25,f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t54_enumset1.p',idempotence_k2_xboole_0)).

fof(f9265,plain,(
    ! [X227,X225,X228,X226,X224] : k2_xboole_0(X228,k2_xboole_0(k1_tarski(X227),k1_enumset1(X224,X225,X226))) = k2_xboole_0(k2_enumset1(X224,X226,X225,X227),k2_xboole_0(k1_tarski(X227),X228)) ),
    inference(superposition,[],[f712,f2085])).

fof(f712,plain,(
    ! [X14,X15,X16] : k2_xboole_0(X16,k2_xboole_0(X14,X15)) = k2_xboole_0(k2_xboole_0(X15,X14),k2_xboole_0(X14,X16)) ),
    inference(superposition,[],[f105,f224])).

fof(f224,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f40,f34])).

fof(f105,plain,(
    ! [X10,X8,X9] : k2_xboole_0(X9,k2_xboole_0(X8,X10)) = k2_xboole_0(X10,k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f35,f22])).

fof(f7666,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f7665])).

fof(f7665,plain,
    ( spl6_1
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f44082,plain,
    ( ~ spl6_3
    | spl6_1 ),
    inference(avatar_split_clause,[],[f18504,f7665,f44080])).

fof(f44080,plain,
    ( spl6_3
  <=> k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK4,sK5),k2_enumset1(sK0,sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f18504,plain,
    ( k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_tarski(sK4,sK5),k2_enumset1(sK0,sK1,sK2,sK3))
    | ~ spl6_1 ),
    inference(superposition,[],[f7666,f22])).

fof(f7667,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f20,f7665])).

fof(f20,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5))
   => k4_enumset1(sK0,sK1,sK2,sK3,sK4,sK5) != k2_xboole_0(k2_enumset1(sK0,sK1,sK2,sK3),k2_tarski(sK4,sK5)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) != k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_tarski(X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t54_enumset1.p',t54_enumset1)).
%------------------------------------------------------------------------------

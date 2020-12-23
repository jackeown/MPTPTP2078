%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0201+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:16 EST 2020

% Result     : Theorem 20.44s
% Output     : Refutation 20.44s
% Verified   : 
% Statistics : Number of formulae       :   28 (  31 expanded)
%              Number of leaves         :    8 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   31 (  35 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17543,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f370,f17479])).

fof(f17479,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f17475])).

fof(f17475,plain,
    ( $false
    | spl9_1 ),
    inference(subsumption_resolution,[],[f369,f17474])).

fof(f17474,plain,(
    ! [X121,X118,X116,X114,X122,X120,X119,X117,X115] : k2_xboole_0(k1_tarski(X120),k6_enumset1(X121,X122,X114,X115,X116,X117,X118,X119)) = k7_enumset1(X120,X121,X122,X114,X115,X116,X117,X118,X119) ),
    inference(forward_demodulation,[],[f17473,f307])).

fof(f307,plain,(
    ! [X6,X4,X2,X0,X8,X7,X5,X3,X1] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    inference(cnf_transformation,[],[f188])).

fof(f188,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k3_enumset1(X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l142_enumset1)).

fof(f17473,plain,(
    ! [X121,X118,X116,X114,X122,X120,X119,X117,X115] : k2_xboole_0(k2_enumset1(X120,X121,X122,X114),k3_enumset1(X115,X116,X117,X118,X119)) = k2_xboole_0(k1_tarski(X120),k6_enumset1(X121,X122,X114,X115,X116,X117,X118,X119)) ),
    inference(forward_demodulation,[],[f17355,f12674])).

fof(f12674,plain,(
    ! [X70,X68,X66,X64,X71,X69,X67,X65,X63] : k2_xboole_0(k1_enumset1(X71,X63,X64),k4_enumset1(X65,X66,X67,X68,X69,X70)) = k2_xboole_0(k1_tarski(X71),k6_enumset1(X63,X64,X65,X66,X67,X68,X69,X70)) ),
    inference(superposition,[],[f532,f287])).

fof(f287,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f236])).

fof(f236,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_enumset1)).

fof(f532,plain,(
    ! [X6,X4,X5,X3] : k2_xboole_0(k1_tarski(X3),k2_xboole_0(k2_tarski(X4,X5),X6)) = k2_xboole_0(k1_enumset1(X3,X4,X5),X6) ),
    inference(superposition,[],[f277,f301])).

fof(f301,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f215])).

fof(f215,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f277,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f113])).

fof(f113,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f17355,plain,(
    ! [X121,X118,X116,X114,X122,X120,X119,X117,X115] : k2_xboole_0(k2_enumset1(X120,X121,X122,X114),k3_enumset1(X115,X116,X117,X118,X119)) = k2_xboole_0(k1_enumset1(X120,X121,X122),k4_enumset1(X114,X115,X116,X117,X118,X119)) ),
    inference(superposition,[],[f644,f331])).

fof(f331,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    inference(cnf_transformation,[],[f224])).

fof(f224,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_tarski(X0),k3_enumset1(X1,X2,X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_enumset1)).

fof(f644,plain,(
    ! [X6,X4,X8,X7,X5] : k2_xboole_0(k1_enumset1(X4,X5,X6),k2_xboole_0(k1_tarski(X7),X8)) = k2_xboole_0(k2_enumset1(X4,X5,X6,X7),X8) ),
    inference(superposition,[],[f277,f298])).

fof(f298,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f219])).

fof(f219,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

fof(f369,plain,
    ( k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f367])).

fof(f367,plain,
    ( spl9_1
  <=> k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) = k2_xboole_0(k1_tarski(sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f370,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f274,f367])).

fof(f274,plain,(
    k7_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8) != k2_xboole_0(k1_tarski(sK0),k6_enumset1(sK1,sK2,sK3,sK4,sK5,sK6,sK7,sK8)) ),
    inference(cnf_transformation,[],[f273])).

fof(f273,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) != k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(ennf_transformation,[],[f213])).

fof(f213,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    inference(negated_conjecture,[],[f212])).

fof(f212,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7,X8] : k7_enumset1(X0,X1,X2,X3,X4,X5,X6,X7,X8) = k2_xboole_0(k1_tarski(X0),k6_enumset1(X1,X2,X3,X4,X5,X6,X7,X8)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t127_enumset1)).
%------------------------------------------------------------------------------

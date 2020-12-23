%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:56 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 887 expanded)
%              Number of leaves         :   28 ( 300 expanded)
%              Depth                    :   17
%              Number of atoms          :  258 (1370 expanded)
%              Number of equality atoms :  164 (1236 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f977,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f91,f98,f379,f385,f409,f964,f976])).

fof(f976,plain,
    ( ~ spl3_1
    | spl3_2
    | spl3_5
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f975])).

fof(f975,plain,
    ( $false
    | ~ spl3_1
    | spl3_2
    | spl3_5
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f974,f97])).

fof(f97,plain,
    ( sK1 != sK2
    | spl3_5 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_5
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f974,plain,
    ( sK1 = sK2
    | ~ spl3_1
    | spl3_2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f973,f81])).

fof(f81,plain,
    ( k1_xboole_0 != sK2
    | spl3_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f973,plain,
    ( k1_xboole_0 = sK2
    | sK1 = sK2
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(resolution,[],[f303,f438])).

fof(f438,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0
        | sK1 = X0 )
    | ~ spl3_1 ),
    inference(superposition,[],[f69,f76])).

fof(f76,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl3_1
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f43,f60,f60])).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f51,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f52,f53])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f51,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f303,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f302])).

fof(f302,plain,
    ( spl3_6
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f964,plain,
    ( spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f961,f381,f302])).

fof(f381,plain,
    ( spl3_8
  <=> sK1 = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f961,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f955,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f955,plain,
    ( k1_xboole_0 != k5_xboole_0(sK2,sK2)
    | r1_tarski(sK2,sK1)
    | ~ spl3_8 ),
    inference(superposition,[],[f123,f432])).

fof(f432,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f427,f176])).

fof(f176,plain,(
    ! [X10,X9] : k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9 ),
    inference(superposition,[],[f156,f156])).

fof(f156,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f151,f38])).

fof(f38,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f151,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f133,f107])).

fof(f107,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f38,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f133,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f49,f33])).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f427,plain,
    ( k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1)
    | ~ spl3_8 ),
    inference(superposition,[],[f156,f383])).

fof(f383,plain,
    ( sK1 = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f381])).

fof(f123,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 != k5_xboole_0(X1,k3_xboole_0(X2,X1))
      | r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f71,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f41])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f409,plain,
    ( ~ spl3_3
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f408])).

fof(f408,plain,
    ( $false
    | ~ spl3_3
    | spl3_4 ),
    inference(subsumption_resolution,[],[f391,f129])).

fof(f129,plain,(
    ! [X5] : r1_tarski(k1_xboole_0,X5) ),
    inference(subsumption_resolution,[],[f125,f33])).

fof(f125,plain,(
    ! [X5] :
      ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
      | r1_tarski(k1_xboole_0,X5) ) ),
    inference(superposition,[],[f71,f99])).

fof(f99,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f37,f32])).

fof(f32,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f391,plain,
    ( ~ r1_tarski(k1_xboole_0,sK2)
    | ~ spl3_3
    | spl3_4 ),
    inference(backward_demodulation,[],[f313,f85])).

fof(f85,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f313,plain,
    ( ~ r1_tarski(sK1,sK2)
    | spl3_4 ),
    inference(subsumption_resolution,[],[f312,f151])).

fof(f312,plain,
    ( sK2 != k5_xboole_0(sK1,k5_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK1,sK2)
    | spl3_4 ),
    inference(superposition,[],[f291,f167])).

fof(f167,plain,(
    ! [X6,X5] :
      ( k3_xboole_0(X5,X6) = X5
      | ~ r1_tarski(X5,X6) ) ),
    inference(forward_demodulation,[],[f158,f34])).

fof(f158,plain,(
    ! [X6,X5] :
      ( k3_xboole_0(X5,X6) = k5_xboole_0(X5,k1_xboole_0)
      | ~ r1_tarski(X5,X6) ) ),
    inference(superposition,[],[f151,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f47,f41])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f291,plain,
    ( sK2 != k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))
    | spl3_4 ),
    inference(superposition,[],[f90,f279])).

fof(f279,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f254,f38])).

fof(f254,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f64,f66])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f42,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f39,f58])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f64,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f28,f60,f59])).

fof(f28,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f90,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl3_4
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f385,plain,
    ( spl3_8
    | spl3_3 ),
    inference(avatar_split_clause,[],[f369,f84,f381])).

fof(f369,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f362,f289])).

fof(f289,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f278,f38])).

fof(f278,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f65,f66])).

fof(f65,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f36,f59])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f362,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)))
      | k1_xboole_0 = X0
      | k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) = X0 ) ),
    inference(superposition,[],[f69,f279])).

fof(f379,plain,
    ( spl3_3
    | spl3_1 ),
    inference(avatar_split_clause,[],[f378,f75,f84])).

fof(f378,plain,
    ( k1_xboole_0 = sK1
    | spl3_1 ),
    inference(subsumption_resolution,[],[f373,f292])).

fof(f292,plain,
    ( sK1 != k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))
    | spl3_1 ),
    inference(superposition,[],[f77,f279])).

fof(f77,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f373,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f362,f290])).

fof(f290,plain,(
    r1_tarski(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f252,f279])).

fof(f252,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f65,f64])).

fof(f98,plain,
    ( ~ spl3_5
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f93,f75,f95])).

fof(f93,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f92])).

fof(f92,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != sK2 ),
    inference(inner_rewriting,[],[f63])).

fof(f63,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f29,f60,f60])).

fof(f29,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f91,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f62,f88,f84])).

fof(f62,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f30,f60])).

fof(f30,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f61,f79,f75])).

fof(f61,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f31,f60])).

fof(f31,plain,
    ( k1_xboole_0 != sK2
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:18:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (1603)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (1626)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (1618)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (1608)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (1626)Refutation not found, incomplete strategy% (1626)------------------------------
% 0.20/0.52  % (1626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (1626)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (1626)Memory used [KB]: 10746
% 0.20/0.52  % (1626)Time elapsed: 0.064 s
% 0.20/0.52  % (1626)------------------------------
% 0.20/0.52  % (1626)------------------------------
% 0.20/0.53  % (1604)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (1628)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (1606)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (1620)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.54  % (1611)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (1627)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.54  % (1602)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.39/0.54  % (1616)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.39/0.55  % (1605)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.39/0.55  % (1612)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.39/0.55  % (1614)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.55  % (1609)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.39/0.55  % (1632)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.39/0.56  % (1610)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.39/0.56  % (1619)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.39/0.56  % (1631)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.39/0.56  % (1619)Refutation not found, incomplete strategy% (1619)------------------------------
% 1.39/0.56  % (1619)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.56  % (1619)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.56  
% 1.39/0.56  % (1619)Memory used [KB]: 6140
% 1.39/0.56  % (1619)Time elapsed: 0.001 s
% 1.39/0.56  % (1619)------------------------------
% 1.39/0.56  % (1619)------------------------------
% 1.39/0.56  % (1630)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.39/0.56  % (1622)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.58/0.56  % (1624)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.58/0.57  % (1624)Refutation not found, incomplete strategy% (1624)------------------------------
% 1.58/0.57  % (1624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (1624)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.57  
% 1.58/0.57  % (1624)Memory used [KB]: 10746
% 1.58/0.57  % (1624)Time elapsed: 0.157 s
% 1.58/0.57  % (1624)------------------------------
% 1.58/0.57  % (1624)------------------------------
% 1.58/0.57  % (1612)Refutation not found, incomplete strategy% (1612)------------------------------
% 1.58/0.57  % (1612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.57  % (1612)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.57  
% 1.58/0.57  % (1612)Memory used [KB]: 10618
% 1.58/0.57  % (1612)Time elapsed: 0.156 s
% 1.58/0.57  % (1612)------------------------------
% 1.58/0.57  % (1612)------------------------------
% 1.58/0.57  % (1607)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.58/0.58  % (1629)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.58/0.58  % (1623)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.58/0.58  % (1621)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.58/0.58  % (1621)Refutation not found, incomplete strategy% (1621)------------------------------
% 1.58/0.58  % (1621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (1621)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  
% 1.58/0.58  % (1621)Memory used [KB]: 10618
% 1.58/0.58  % (1621)Time elapsed: 0.172 s
% 1.58/0.58  % (1621)------------------------------
% 1.58/0.58  % (1621)------------------------------
% 1.58/0.58  % (1633)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.58/0.59  % (1613)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.58/0.59  % (1625)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.58/0.61  % (1631)Refutation found. Thanks to Tanya!
% 1.58/0.61  % SZS status Theorem for theBenchmark
% 1.58/0.61  % SZS output start Proof for theBenchmark
% 1.58/0.61  fof(f977,plain,(
% 1.58/0.61    $false),
% 1.58/0.61    inference(avatar_sat_refutation,[],[f82,f91,f98,f379,f385,f409,f964,f976])).
% 1.58/0.61  fof(f976,plain,(
% 1.58/0.61    ~spl3_1 | spl3_2 | spl3_5 | ~spl3_6),
% 1.58/0.61    inference(avatar_contradiction_clause,[],[f975])).
% 1.58/0.61  fof(f975,plain,(
% 1.58/0.61    $false | (~spl3_1 | spl3_2 | spl3_5 | ~spl3_6)),
% 1.58/0.61    inference(subsumption_resolution,[],[f974,f97])).
% 1.58/0.61  fof(f97,plain,(
% 1.58/0.61    sK1 != sK2 | spl3_5),
% 1.58/0.61    inference(avatar_component_clause,[],[f95])).
% 1.58/0.61  fof(f95,plain,(
% 1.58/0.61    spl3_5 <=> sK1 = sK2),
% 1.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.58/0.61  fof(f974,plain,(
% 1.58/0.61    sK1 = sK2 | (~spl3_1 | spl3_2 | ~spl3_6)),
% 1.58/0.61    inference(subsumption_resolution,[],[f973,f81])).
% 1.58/0.61  fof(f81,plain,(
% 1.58/0.61    k1_xboole_0 != sK2 | spl3_2),
% 1.58/0.61    inference(avatar_component_clause,[],[f79])).
% 1.58/0.61  fof(f79,plain,(
% 1.58/0.61    spl3_2 <=> k1_xboole_0 = sK2),
% 1.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.58/0.61  fof(f973,plain,(
% 1.58/0.61    k1_xboole_0 = sK2 | sK1 = sK2 | (~spl3_1 | ~spl3_6)),
% 1.58/0.61    inference(resolution,[],[f303,f438])).
% 1.58/0.61  fof(f438,plain,(
% 1.58/0.61    ( ! [X0] : (~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | sK1 = X0) ) | ~spl3_1),
% 1.58/0.61    inference(superposition,[],[f69,f76])).
% 1.58/0.61  fof(f76,plain,(
% 1.58/0.61    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~spl3_1),
% 1.58/0.61    inference(avatar_component_clause,[],[f75])).
% 1.58/0.61  fof(f75,plain,(
% 1.58/0.61    spl3_1 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.58/0.61  fof(f69,plain,(
% 1.58/0.61    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0) )),
% 1.58/0.61    inference(definition_unfolding,[],[f43,f60,f60])).
% 1.58/0.61  fof(f60,plain,(
% 1.58/0.61    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.58/0.61    inference(definition_unfolding,[],[f35,f58])).
% 1.58/0.61  fof(f58,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.58/0.61    inference(definition_unfolding,[],[f40,f57])).
% 1.58/0.61  fof(f57,plain,(
% 1.58/0.61    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.58/0.61    inference(definition_unfolding,[],[f48,f56])).
% 1.58/0.61  fof(f56,plain,(
% 1.58/0.61    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.58/0.61    inference(definition_unfolding,[],[f50,f55])).
% 1.58/0.61  fof(f55,plain,(
% 1.58/0.61    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.58/0.61    inference(definition_unfolding,[],[f51,f54])).
% 1.58/0.61  fof(f54,plain,(
% 1.58/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.58/0.61    inference(definition_unfolding,[],[f52,f53])).
% 1.58/0.61  fof(f53,plain,(
% 1.58/0.61    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f17])).
% 1.58/0.61  fof(f17,axiom,(
% 1.58/0.61    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.58/0.61  fof(f52,plain,(
% 1.58/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f16])).
% 1.58/0.61  fof(f16,axiom,(
% 1.58/0.61    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.58/0.61  fof(f51,plain,(
% 1.58/0.61    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f15])).
% 1.58/0.61  fof(f15,axiom,(
% 1.58/0.61    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.58/0.61  fof(f50,plain,(
% 1.58/0.61    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f14])).
% 1.58/0.61  fof(f14,axiom,(
% 1.58/0.61    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.58/0.61  fof(f48,plain,(
% 1.58/0.61    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f13])).
% 1.58/0.61  fof(f13,axiom,(
% 1.58/0.61    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.58/0.61  fof(f40,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f12])).
% 1.58/0.61  fof(f12,axiom,(
% 1.58/0.61    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.58/0.61  fof(f35,plain,(
% 1.58/0.61    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f11])).
% 1.58/0.61  fof(f11,axiom,(
% 1.58/0.61    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.58/0.61  fof(f43,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.58/0.61    inference(cnf_transformation,[],[f26])).
% 1.58/0.61  fof(f26,plain,(
% 1.58/0.61    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.58/0.61    inference(flattening,[],[f25])).
% 1.58/0.61  fof(f25,plain,(
% 1.58/0.61    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.58/0.61    inference(nnf_transformation,[],[f18])).
% 1.58/0.61  fof(f18,axiom,(
% 1.58/0.61    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.58/0.61  fof(f303,plain,(
% 1.58/0.61    r1_tarski(sK2,sK1) | ~spl3_6),
% 1.58/0.61    inference(avatar_component_clause,[],[f302])).
% 1.58/0.61  fof(f302,plain,(
% 1.58/0.61    spl3_6 <=> r1_tarski(sK2,sK1)),
% 1.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.58/0.61  fof(f964,plain,(
% 1.58/0.61    spl3_6 | ~spl3_8),
% 1.58/0.61    inference(avatar_split_clause,[],[f961,f381,f302])).
% 1.58/0.61  fof(f381,plain,(
% 1.58/0.61    spl3_8 <=> sK1 = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))),
% 1.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.58/0.61  fof(f961,plain,(
% 1.58/0.61    r1_tarski(sK2,sK1) | ~spl3_8),
% 1.58/0.61    inference(subsumption_resolution,[],[f955,f33])).
% 1.58/0.61  fof(f33,plain,(
% 1.58/0.61    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f9])).
% 1.58/0.61  fof(f9,axiom,(
% 1.58/0.61    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.58/0.61  fof(f955,plain,(
% 1.58/0.61    k1_xboole_0 != k5_xboole_0(sK2,sK2) | r1_tarski(sK2,sK1) | ~spl3_8),
% 1.58/0.61    inference(superposition,[],[f123,f432])).
% 1.58/0.61  fof(f432,plain,(
% 1.58/0.61    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_8),
% 1.58/0.61    inference(forward_demodulation,[],[f427,f176])).
% 1.58/0.61  fof(f176,plain,(
% 1.58/0.61    ( ! [X10,X9] : (k5_xboole_0(k5_xboole_0(X10,X9),X10) = X9) )),
% 1.58/0.61    inference(superposition,[],[f156,f156])).
% 1.58/0.61  fof(f156,plain,(
% 1.58/0.61    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.58/0.61    inference(superposition,[],[f151,f38])).
% 1.58/0.61  fof(f38,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f2])).
% 1.58/0.61  fof(f2,axiom,(
% 1.58/0.61    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.58/0.61  fof(f151,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.58/0.61    inference(forward_demodulation,[],[f133,f107])).
% 1.58/0.61  fof(f107,plain,(
% 1.58/0.61    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.58/0.61    inference(superposition,[],[f38,f34])).
% 1.58/0.61  fof(f34,plain,(
% 1.58/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.58/0.61    inference(cnf_transformation,[],[f6])).
% 1.58/0.61  fof(f6,axiom,(
% 1.58/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.58/0.61  fof(f133,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.58/0.61    inference(superposition,[],[f49,f33])).
% 1.58/0.61  fof(f49,plain,(
% 1.58/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.58/0.61    inference(cnf_transformation,[],[f8])).
% 1.58/0.61  fof(f8,axiom,(
% 1.58/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.58/0.61  fof(f427,plain,(
% 1.58/0.61    k3_xboole_0(sK1,sK2) = k5_xboole_0(k5_xboole_0(sK1,sK2),sK1) | ~spl3_8),
% 1.58/0.61    inference(superposition,[],[f156,f383])).
% 1.58/0.61  fof(f383,plain,(
% 1.58/0.61    sK1 = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) | ~spl3_8),
% 1.58/0.61    inference(avatar_component_clause,[],[f381])).
% 1.58/0.61  fof(f123,plain,(
% 1.58/0.61    ( ! [X2,X1] : (k1_xboole_0 != k5_xboole_0(X1,k3_xboole_0(X2,X1)) | r1_tarski(X1,X2)) )),
% 1.58/0.61    inference(superposition,[],[f71,f37])).
% 1.58/0.61  fof(f37,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f1])).
% 1.58/0.61  fof(f1,axiom,(
% 1.58/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.58/0.61  fof(f71,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) | r1_tarski(X0,X1)) )),
% 1.58/0.61    inference(definition_unfolding,[],[f46,f41])).
% 1.58/0.61  fof(f41,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.58/0.61    inference(cnf_transformation,[],[f4])).
% 1.58/0.61  fof(f4,axiom,(
% 1.58/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.58/0.61  fof(f46,plain,(
% 1.58/0.61    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.58/0.61    inference(cnf_transformation,[],[f27])).
% 1.58/0.61  fof(f27,plain,(
% 1.58/0.61    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.58/0.61    inference(nnf_transformation,[],[f3])).
% 1.58/0.61  fof(f3,axiom,(
% 1.58/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.58/0.61  fof(f409,plain,(
% 1.58/0.61    ~spl3_3 | spl3_4),
% 1.58/0.61    inference(avatar_contradiction_clause,[],[f408])).
% 1.58/0.61  fof(f408,plain,(
% 1.58/0.61    $false | (~spl3_3 | spl3_4)),
% 1.58/0.61    inference(subsumption_resolution,[],[f391,f129])).
% 1.58/0.61  fof(f129,plain,(
% 1.58/0.61    ( ! [X5] : (r1_tarski(k1_xboole_0,X5)) )),
% 1.58/0.61    inference(subsumption_resolution,[],[f125,f33])).
% 1.58/0.61  fof(f125,plain,(
% 1.58/0.61    ( ! [X5] : (k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | r1_tarski(k1_xboole_0,X5)) )),
% 1.58/0.61    inference(superposition,[],[f71,f99])).
% 1.58/0.61  fof(f99,plain,(
% 1.58/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.58/0.61    inference(superposition,[],[f37,f32])).
% 1.58/0.61  fof(f32,plain,(
% 1.58/0.61    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f5])).
% 1.58/0.61  fof(f5,axiom,(
% 1.58/0.61    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.58/0.61  fof(f391,plain,(
% 1.58/0.61    ~r1_tarski(k1_xboole_0,sK2) | (~spl3_3 | spl3_4)),
% 1.58/0.61    inference(backward_demodulation,[],[f313,f85])).
% 1.58/0.61  fof(f85,plain,(
% 1.58/0.61    k1_xboole_0 = sK1 | ~spl3_3),
% 1.58/0.61    inference(avatar_component_clause,[],[f84])).
% 1.58/0.61  fof(f84,plain,(
% 1.58/0.61    spl3_3 <=> k1_xboole_0 = sK1),
% 1.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.58/0.61  fof(f313,plain,(
% 1.58/0.61    ~r1_tarski(sK1,sK2) | spl3_4),
% 1.58/0.61    inference(subsumption_resolution,[],[f312,f151])).
% 1.58/0.61  fof(f312,plain,(
% 1.58/0.61    sK2 != k5_xboole_0(sK1,k5_xboole_0(sK1,sK2)) | ~r1_tarski(sK1,sK2) | spl3_4),
% 1.58/0.61    inference(superposition,[],[f291,f167])).
% 1.58/0.61  fof(f167,plain,(
% 1.58/0.61    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = X5 | ~r1_tarski(X5,X6)) )),
% 1.58/0.61    inference(forward_demodulation,[],[f158,f34])).
% 1.58/0.61  fof(f158,plain,(
% 1.58/0.61    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k5_xboole_0(X5,k1_xboole_0) | ~r1_tarski(X5,X6)) )),
% 1.58/0.61    inference(superposition,[],[f151,f70])).
% 1.58/0.61  fof(f70,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 1.58/0.61    inference(definition_unfolding,[],[f47,f41])).
% 1.58/0.61  fof(f47,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.58/0.61    inference(cnf_transformation,[],[f27])).
% 1.58/0.61  fof(f291,plain,(
% 1.58/0.61    sK2 != k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) | spl3_4),
% 1.58/0.61    inference(superposition,[],[f90,f279])).
% 1.58/0.61  fof(f279,plain,(
% 1.58/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))),
% 1.58/0.61    inference(forward_demodulation,[],[f254,f38])).
% 1.58/0.61  fof(f254,plain,(
% 1.58/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))),
% 1.58/0.61    inference(backward_demodulation,[],[f64,f66])).
% 1.58/0.61  fof(f66,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.58/0.61    inference(definition_unfolding,[],[f42,f59])).
% 1.58/0.61  fof(f59,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.58/0.61    inference(definition_unfolding,[],[f39,f58])).
% 1.58/0.61  fof(f39,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.58/0.61    inference(cnf_transformation,[],[f19])).
% 1.58/0.61  fof(f19,axiom,(
% 1.58/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.58/0.61  fof(f42,plain,(
% 1.58/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.58/0.61    inference(cnf_transformation,[],[f10])).
% 1.58/0.61  fof(f10,axiom,(
% 1.58/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.58/0.61  fof(f64,plain,(
% 1.58/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.58/0.61    inference(definition_unfolding,[],[f28,f60,f59])).
% 1.58/0.61  fof(f28,plain,(
% 1.58/0.61    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.58/0.61    inference(cnf_transformation,[],[f24])).
% 1.58/0.61  fof(f24,plain,(
% 1.58/0.61    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.58/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f23])).
% 1.58/0.61  fof(f23,plain,(
% 1.58/0.61    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.58/0.61    introduced(choice_axiom,[])).
% 1.58/0.61  fof(f22,plain,(
% 1.58/0.61    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.58/0.61    inference(ennf_transformation,[],[f21])).
% 1.58/0.61  fof(f21,negated_conjecture,(
% 1.58/0.61    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.58/0.61    inference(negated_conjecture,[],[f20])).
% 1.58/0.61  fof(f20,conjecture,(
% 1.58/0.61    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.58/0.61  fof(f90,plain,(
% 1.58/0.61    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl3_4),
% 1.58/0.61    inference(avatar_component_clause,[],[f88])).
% 1.58/0.61  fof(f88,plain,(
% 1.58/0.61    spl3_4 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.58/0.61    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.58/0.61  fof(f385,plain,(
% 1.58/0.61    spl3_8 | spl3_3),
% 1.58/0.61    inference(avatar_split_clause,[],[f369,f84,f381])).
% 1.58/0.61  fof(f369,plain,(
% 1.58/0.61    k1_xboole_0 = sK1 | sK1 = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))),
% 1.58/0.61    inference(resolution,[],[f362,f289])).
% 1.58/0.61  fof(f289,plain,(
% 1.58/0.61    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)))) )),
% 1.58/0.61    inference(forward_demodulation,[],[f278,f38])).
% 1.58/0.61  fof(f278,plain,(
% 1.58/0.61    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 1.58/0.61    inference(superposition,[],[f65,f66])).
% 1.58/0.61  fof(f65,plain,(
% 1.58/0.61    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.58/0.61    inference(definition_unfolding,[],[f36,f59])).
% 1.58/0.61  fof(f36,plain,(
% 1.58/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.58/0.61    inference(cnf_transformation,[],[f7])).
% 1.58/0.61  fof(f7,axiom,(
% 1.58/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.58/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.58/0.61  fof(f362,plain,(
% 1.58/0.61    ( ! [X0] : (~r1_tarski(X0,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))) | k1_xboole_0 = X0 | k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) = X0) )),
% 1.58/0.61    inference(superposition,[],[f69,f279])).
% 1.58/0.61  fof(f379,plain,(
% 1.58/0.61    spl3_3 | spl3_1),
% 1.58/0.61    inference(avatar_split_clause,[],[f378,f75,f84])).
% 1.58/0.61  fof(f378,plain,(
% 1.58/0.61    k1_xboole_0 = sK1 | spl3_1),
% 1.58/0.61    inference(subsumption_resolution,[],[f373,f292])).
% 1.58/0.61  fof(f292,plain,(
% 1.58/0.61    sK1 != k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) | spl3_1),
% 1.58/0.61    inference(superposition,[],[f77,f279])).
% 1.58/0.61  fof(f77,plain,(
% 1.58/0.61    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl3_1),
% 1.58/0.61    inference(avatar_component_clause,[],[f75])).
% 1.58/0.61  fof(f373,plain,(
% 1.58/0.61    k1_xboole_0 = sK1 | sK1 = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))),
% 1.58/0.61    inference(resolution,[],[f362,f290])).
% 1.58/0.61  fof(f290,plain,(
% 1.58/0.61    r1_tarski(sK1,k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)))),
% 1.58/0.61    inference(backward_demodulation,[],[f252,f279])).
% 1.58/0.61  fof(f252,plain,(
% 1.58/0.61    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 1.58/0.61    inference(superposition,[],[f65,f64])).
% 1.58/0.61  fof(f98,plain,(
% 1.58/0.61    ~spl3_5 | ~spl3_1),
% 1.58/0.61    inference(avatar_split_clause,[],[f93,f75,f95])).
% 1.58/0.61  fof(f93,plain,(
% 1.58/0.61    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 1.58/0.61    inference(inner_rewriting,[],[f92])).
% 1.58/0.61  fof(f92,plain,(
% 1.58/0.61    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != sK2),
% 1.58/0.61    inference(inner_rewriting,[],[f63])).
% 1.58/0.61  fof(f63,plain,(
% 1.58/0.61    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.58/0.61    inference(definition_unfolding,[],[f29,f60,f60])).
% 1.58/0.61  fof(f29,plain,(
% 1.58/0.61    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.58/0.61    inference(cnf_transformation,[],[f24])).
% 1.58/0.61  fof(f91,plain,(
% 1.58/0.61    ~spl3_3 | ~spl3_4),
% 1.58/0.61    inference(avatar_split_clause,[],[f62,f88,f84])).
% 1.58/0.61  fof(f62,plain,(
% 1.58/0.61    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 1.58/0.61    inference(definition_unfolding,[],[f30,f60])).
% 1.58/0.61  fof(f30,plain,(
% 1.58/0.61    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.58/0.61    inference(cnf_transformation,[],[f24])).
% 1.58/0.61  fof(f82,plain,(
% 1.58/0.61    ~spl3_1 | ~spl3_2),
% 1.58/0.61    inference(avatar_split_clause,[],[f61,f79,f75])).
% 1.58/0.61  fof(f61,plain,(
% 1.58/0.61    k1_xboole_0 != sK2 | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.58/0.61    inference(definition_unfolding,[],[f31,f60])).
% 1.58/0.61  fof(f31,plain,(
% 1.58/0.61    k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)),
% 1.58/0.61    inference(cnf_transformation,[],[f24])).
% 1.58/0.61  % SZS output end Proof for theBenchmark
% 1.58/0.61  % (1631)------------------------------
% 1.58/0.61  % (1631)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.61  % (1631)Termination reason: Refutation
% 1.58/0.61  
% 1.58/0.61  % (1631)Memory used [KB]: 6780
% 1.58/0.61  % (1631)Time elapsed: 0.182 s
% 1.58/0.61  % (1631)------------------------------
% 1.58/0.61  % (1631)------------------------------
% 1.58/0.61  % (1600)Success in time 0.255 s
%------------------------------------------------------------------------------

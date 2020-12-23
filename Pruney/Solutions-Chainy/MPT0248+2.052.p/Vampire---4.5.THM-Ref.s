%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:56 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 484 expanded)
%              Number of leaves         :   28 ( 177 expanded)
%              Depth                    :   17
%              Number of atoms          :  195 ( 664 expanded)
%              Number of equality atoms :  115 ( 541 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1632,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f82,f87,f92,f187,f524,f617,f618,f1562,f1563,f1596])).

fof(f1596,plain,
    ( spl3_2
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f1595,f521,f84,f75])).

fof(f75,plain,
    ( spl3_2
  <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f84,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f521,plain,
    ( spl3_14
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f1595,plain,
    ( sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f1594,f29])).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f1594,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f1593,f107])).

fof(f107,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f104,f93])).

fof(f93,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f33,f29])).

fof(f33,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f104,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(resolution,[],[f66,f27])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f41,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1593,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK2))
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f1567,f93])).

fof(f1567,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK2)))
    | ~ spl3_4
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f523,f85])).

fof(f85,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f523,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f521])).

fof(f1563,plain,
    ( spl3_4
    | spl3_18
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f1558,f521,f583,f84])).

fof(f583,plain,
    ( spl3_18
  <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f1558,plain,
    ( sK1 = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))
    | k1_xboole_0 = sK1
    | ~ spl3_14 ),
    inference(resolution,[],[f615,f605])).

fof(f605,plain,(
    ! [X2,X1] : r1_tarski(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) ),
    inference(forward_demodulation,[],[f598,f33])).

fof(f598,plain,(
    ! [X2,X1] : r1_tarski(X2,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),X1))) ),
    inference(superposition,[],[f525,f125])).

fof(f125,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f44,f33])).

fof(f44,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f525,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1)))) ),
    inference(forward_demodulation,[],[f424,f33])).

fof(f424,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X0,X1),X0))) ),
    inference(backward_demodulation,[],[f161,f125])).

fof(f161,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f156,f33])).

fof(f156,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f60,f61])).

fof(f61,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f43,f51])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f45,f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f46,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f47,f48])).

fof(f48,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f31,f54])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f615,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))))
        | k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) = X0
        | k1_xboole_0 = X0 )
    | ~ spl3_14 ),
    inference(superposition,[],[f64,f523])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f38,f55,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f53])).

fof(f30,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f1562,plain,
    ( spl3_5
    | spl3_17
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f1557,f521,f578,f89])).

fof(f89,plain,
    ( spl3_5
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f578,plain,
    ( spl3_17
  <=> sK2 = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f1557,plain,
    ( sK2 = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))
    | k1_xboole_0 = sK2
    | ~ spl3_14 ),
    inference(resolution,[],[f615,f589])).

fof(f589,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) ),
    inference(superposition,[],[f525,f32])).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f618,plain,
    ( ~ spl3_17
    | spl3_2
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f612,f521,f75,f578])).

fof(f612,plain,
    ( sK2 != k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))
    | spl3_2
    | ~ spl3_14 ),
    inference(superposition,[],[f77,f523])).

fof(f77,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f617,plain,
    ( ~ spl3_18
    | spl3_3
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f611,f521,f79,f583])).

fof(f79,plain,
    ( spl3_3
  <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f611,plain,
    ( sK1 != k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))
    | spl3_3
    | ~ spl3_14 ),
    inference(superposition,[],[f81,f523])).

fof(f81,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f524,plain,
    ( spl3_14
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f519,f184,f521])).

fof(f184,plain,
    ( spl3_6
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f519,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f423,f125])).

fof(f423,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),sK1))
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f186,f125])).

fof(f186,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f184])).

fof(f187,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f182,f70,f184])).

fof(f70,plain,
    ( spl3_1
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f182,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f181,f33])).

fof(f181,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f72,f61])).

fof(f72,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f92,plain,
    ( ~ spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f59,f79,f89])).

fof(f59,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f23,f55])).

fof(f23,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f22])).

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

fof(f87,plain,
    ( ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f58,f84,f75])).

fof(f58,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f24,f55])).

fof(f24,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f57,f79,f75])).

fof(f57,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f25,f55,f55])).

fof(f25,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f73,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f56,f70])).

fof(f56,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f26,f55,f54])).

fof(f26,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (20373)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.50  % (20381)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (20369)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (20375)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (20366)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (20365)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (20365)Refutation not found, incomplete strategy% (20365)------------------------------
% 0.20/0.53  % (20365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (20365)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (20365)Memory used [KB]: 1663
% 0.20/0.53  % (20365)Time elapsed: 0.112 s
% 0.20/0.53  % (20365)------------------------------
% 0.20/0.53  % (20365)------------------------------
% 0.20/0.53  % (20376)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (20388)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (20389)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (20367)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (20370)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.54  % (20390)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (20380)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (20380)Refutation not found, incomplete strategy% (20380)------------------------------
% 0.20/0.54  % (20380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (20380)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (20380)Memory used [KB]: 6140
% 0.20/0.54  % (20380)Time elapsed: 0.001 s
% 0.20/0.54  % (20380)------------------------------
% 0.20/0.54  % (20380)------------------------------
% 0.20/0.54  % (20394)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (20374)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (20375)Refutation not found, incomplete strategy% (20375)------------------------------
% 0.20/0.54  % (20375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (20375)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (20375)Memory used [KB]: 10618
% 0.20/0.54  % (20375)Time elapsed: 0.123 s
% 0.20/0.54  % (20375)------------------------------
% 0.20/0.54  % (20375)------------------------------
% 0.20/0.54  % (20386)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (20371)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (20379)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (20383)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (20395)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (20368)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  % (20372)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.55  % (20387)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (20393)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (20377)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (20376)Refutation not found, incomplete strategy% (20376)------------------------------
% 0.20/0.55  % (20376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (20376)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (20376)Memory used [KB]: 10618
% 0.20/0.55  % (20376)Time elapsed: 0.141 s
% 0.20/0.55  % (20376)------------------------------
% 0.20/0.55  % (20376)------------------------------
% 0.20/0.55  % (20388)Refutation not found, incomplete strategy% (20388)------------------------------
% 0.20/0.55  % (20388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (20391)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.55  % (20378)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (20388)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (20388)Memory used [KB]: 10746
% 0.20/0.55  % (20388)Time elapsed: 0.120 s
% 0.20/0.55  % (20388)------------------------------
% 0.20/0.55  % (20388)------------------------------
% 0.20/0.55  % (20384)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (20392)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (20386)Refutation not found, incomplete strategy% (20386)------------------------------
% 0.20/0.55  % (20386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (20382)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.56  % (20382)Refutation not found, incomplete strategy% (20382)------------------------------
% 0.20/0.56  % (20382)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (20382)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (20382)Memory used [KB]: 10618
% 0.20/0.56  % (20382)Time elapsed: 0.148 s
% 0.20/0.56  % (20382)------------------------------
% 0.20/0.56  % (20382)------------------------------
% 1.57/0.56  % (20386)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.56  
% 1.57/0.56  % (20386)Memory used [KB]: 10746
% 1.57/0.56  % (20386)Time elapsed: 0.129 s
% 1.57/0.56  % (20386)------------------------------
% 1.57/0.56  % (20386)------------------------------
% 1.57/0.57  % (20381)Refutation found. Thanks to Tanya!
% 1.57/0.57  % SZS status Theorem for theBenchmark
% 1.72/0.60  % SZS output start Proof for theBenchmark
% 1.72/0.60  fof(f1632,plain,(
% 1.72/0.60    $false),
% 1.72/0.60    inference(avatar_sat_refutation,[],[f73,f82,f87,f92,f187,f524,f617,f618,f1562,f1563,f1596])).
% 1.72/0.60  fof(f1596,plain,(
% 1.72/0.60    spl3_2 | ~spl3_4 | ~spl3_14),
% 1.72/0.60    inference(avatar_split_clause,[],[f1595,f521,f84,f75])).
% 1.72/0.60  fof(f75,plain,(
% 1.72/0.60    spl3_2 <=> sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.72/0.60  fof(f84,plain,(
% 1.72/0.60    spl3_4 <=> k1_xboole_0 = sK1),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.72/0.60  fof(f521,plain,(
% 1.72/0.60    spl3_14 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.72/0.60  fof(f1595,plain,(
% 1.72/0.60    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | (~spl3_4 | ~spl3_14)),
% 1.72/0.60    inference(forward_demodulation,[],[f1594,f29])).
% 1.72/0.60  fof(f29,plain,(
% 1.72/0.60    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.72/0.60    inference(cnf_transformation,[],[f6])).
% 1.72/0.60  fof(f6,axiom,(
% 1.72/0.60    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.72/0.60  fof(f1594,plain,(
% 1.72/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k1_xboole_0) | (~spl3_4 | ~spl3_14)),
% 1.72/0.60    inference(forward_demodulation,[],[f1593,f107])).
% 1.72/0.60  fof(f107,plain,(
% 1.72/0.60    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 1.72/0.60    inference(superposition,[],[f104,f93])).
% 1.72/0.60  fof(f93,plain,(
% 1.72/0.60    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 1.72/0.60    inference(superposition,[],[f33,f29])).
% 1.72/0.60  fof(f33,plain,(
% 1.72/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f2])).
% 1.72/0.60  fof(f2,axiom,(
% 1.72/0.60    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.72/0.60  fof(f104,plain,(
% 1.72/0.60    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.72/0.60    inference(resolution,[],[f66,f27])).
% 1.72/0.60  fof(f27,plain,(
% 1.72/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f5])).
% 1.72/0.60  fof(f5,axiom,(
% 1.72/0.60    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.72/0.60  fof(f66,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.72/0.60    inference(definition_unfolding,[],[f41,f36])).
% 1.72/0.60  fof(f36,plain,(
% 1.72/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.72/0.60    inference(cnf_transformation,[],[f4])).
% 1.72/0.60  fof(f4,axiom,(
% 1.72/0.60    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.72/0.60  fof(f41,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.72/0.60    inference(cnf_transformation,[],[f3])).
% 1.72/0.60  fof(f3,axiom,(
% 1.72/0.60    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.72/0.60  fof(f1593,plain,(
% 1.72/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK2)) | (~spl3_4 | ~spl3_14)),
% 1.72/0.60    inference(forward_demodulation,[],[f1567,f93])).
% 1.72/0.60  fof(f1567,plain,(
% 1.72/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k3_xboole_0(k1_xboole_0,sK2))) | (~spl3_4 | ~spl3_14)),
% 1.72/0.60    inference(backward_demodulation,[],[f523,f85])).
% 1.72/0.60  fof(f85,plain,(
% 1.72/0.60    k1_xboole_0 = sK1 | ~spl3_4),
% 1.72/0.60    inference(avatar_component_clause,[],[f84])).
% 1.72/0.60  fof(f523,plain,(
% 1.72/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) | ~spl3_14),
% 1.72/0.60    inference(avatar_component_clause,[],[f521])).
% 1.72/0.60  fof(f1563,plain,(
% 1.72/0.60    spl3_4 | spl3_18 | ~spl3_14),
% 1.72/0.60    inference(avatar_split_clause,[],[f1558,f521,f583,f84])).
% 1.72/0.60  fof(f583,plain,(
% 1.72/0.60    spl3_18 <=> sK1 = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.72/0.60  fof(f1558,plain,(
% 1.72/0.60    sK1 = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) | k1_xboole_0 = sK1 | ~spl3_14),
% 1.72/0.60    inference(resolution,[],[f615,f605])).
% 1.72/0.60  fof(f605,plain,(
% 1.72/0.60    ( ! [X2,X1] : (r1_tarski(X2,k5_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))))) )),
% 1.72/0.60    inference(forward_demodulation,[],[f598,f33])).
% 1.72/0.60  fof(f598,plain,(
% 1.72/0.60    ( ! [X2,X1] : (r1_tarski(X2,k5_xboole_0(X2,k5_xboole_0(k3_xboole_0(X2,X1),X1)))) )),
% 1.72/0.60    inference(superposition,[],[f525,f125])).
% 1.72/0.60  fof(f125,plain,(
% 1.72/0.60    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 1.72/0.60    inference(superposition,[],[f44,f33])).
% 1.72/0.60  fof(f44,plain,(
% 1.72/0.60    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.72/0.60    inference(cnf_transformation,[],[f8])).
% 1.72/0.60  fof(f8,axiom,(
% 1.72/0.60    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.72/0.60  fof(f525,plain,(
% 1.72/0.60    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X0,X1))))) )),
% 1.72/0.60    inference(forward_demodulation,[],[f424,f33])).
% 1.72/0.60  fof(f424,plain,(
% 1.72/0.60    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(k3_xboole_0(X0,X1),X0)))) )),
% 1.72/0.60    inference(backward_demodulation,[],[f161,f125])).
% 1.72/0.60  fof(f161,plain,(
% 1.72/0.60    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)))) )),
% 1.72/0.60    inference(forward_demodulation,[],[f156,f33])).
% 1.72/0.60  fof(f156,plain,(
% 1.72/0.60    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)))) )),
% 1.72/0.60    inference(superposition,[],[f60,f61])).
% 1.72/0.60  fof(f61,plain,(
% 1.72/0.60    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.72/0.60    inference(definition_unfolding,[],[f37,f54])).
% 1.72/0.60  fof(f54,plain,(
% 1.72/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.72/0.60    inference(definition_unfolding,[],[f34,f53])).
% 1.72/0.60  fof(f53,plain,(
% 1.72/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.72/0.60    inference(definition_unfolding,[],[f35,f52])).
% 1.72/0.60  fof(f52,plain,(
% 1.72/0.60    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.72/0.60    inference(definition_unfolding,[],[f43,f51])).
% 1.72/0.60  fof(f51,plain,(
% 1.72/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.72/0.60    inference(definition_unfolding,[],[f45,f50])).
% 1.72/0.60  fof(f50,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.72/0.60    inference(definition_unfolding,[],[f46,f49])).
% 1.72/0.60  fof(f49,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.72/0.60    inference(definition_unfolding,[],[f47,f48])).
% 1.72/0.60  fof(f48,plain,(
% 1.72/0.60    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f17])).
% 1.72/0.60  fof(f17,axiom,(
% 1.72/0.60    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.72/0.60  fof(f47,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f16])).
% 1.72/0.60  fof(f16,axiom,(
% 1.72/0.60    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.72/0.60  fof(f46,plain,(
% 1.72/0.60    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f15])).
% 1.72/0.60  fof(f15,axiom,(
% 1.72/0.60    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.72/0.60  fof(f45,plain,(
% 1.72/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f14])).
% 1.72/0.60  fof(f14,axiom,(
% 1.72/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.72/0.60  fof(f43,plain,(
% 1.72/0.60    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f13])).
% 1.72/0.60  fof(f13,axiom,(
% 1.72/0.60    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.72/0.60  fof(f35,plain,(
% 1.72/0.60    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f12])).
% 1.72/0.60  fof(f12,axiom,(
% 1.72/0.60    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.72/0.60  fof(f34,plain,(
% 1.72/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.72/0.60    inference(cnf_transformation,[],[f19])).
% 1.72/0.60  fof(f19,axiom,(
% 1.72/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.72/0.60  fof(f37,plain,(
% 1.72/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.72/0.60    inference(cnf_transformation,[],[f10])).
% 1.72/0.60  fof(f10,axiom,(
% 1.72/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.72/0.60  fof(f60,plain,(
% 1.72/0.60    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.72/0.60    inference(definition_unfolding,[],[f31,f54])).
% 1.72/0.60  fof(f31,plain,(
% 1.72/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.72/0.60    inference(cnf_transformation,[],[f7])).
% 1.72/0.60  fof(f7,axiom,(
% 1.72/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.72/0.60  fof(f615,plain,(
% 1.72/0.60    ( ! [X0] : (~r1_tarski(X0,k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))) | k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) = X0 | k1_xboole_0 = X0) ) | ~spl3_14),
% 1.72/0.60    inference(superposition,[],[f64,f523])).
% 1.72/0.60  fof(f64,plain,(
% 1.72/0.60    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 1.72/0.60    inference(definition_unfolding,[],[f38,f55,f55])).
% 1.72/0.60  fof(f55,plain,(
% 1.72/0.60    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.72/0.60    inference(definition_unfolding,[],[f30,f53])).
% 1.72/0.60  fof(f30,plain,(
% 1.72/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f11])).
% 1.72/0.60  fof(f11,axiom,(
% 1.72/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.72/0.60  fof(f38,plain,(
% 1.72/0.60    ( ! [X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 1.72/0.60    inference(cnf_transformation,[],[f18])).
% 1.72/0.60  fof(f18,axiom,(
% 1.72/0.60    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.72/0.60  fof(f1562,plain,(
% 1.72/0.60    spl3_5 | spl3_17 | ~spl3_14),
% 1.72/0.60    inference(avatar_split_clause,[],[f1557,f521,f578,f89])).
% 1.72/0.60  fof(f89,plain,(
% 1.72/0.60    spl3_5 <=> k1_xboole_0 = sK2),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.72/0.60  fof(f578,plain,(
% 1.72/0.60    spl3_17 <=> sK2 = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2)))),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.72/0.60  fof(f1557,plain,(
% 1.72/0.60    sK2 = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) | k1_xboole_0 = sK2 | ~spl3_14),
% 1.72/0.60    inference(resolution,[],[f615,f589])).
% 1.72/0.60  fof(f589,plain,(
% 1.72/0.60    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) )),
% 1.72/0.60    inference(superposition,[],[f525,f32])).
% 1.72/0.60  fof(f32,plain,(
% 1.72/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.72/0.60    inference(cnf_transformation,[],[f1])).
% 1.72/0.60  fof(f1,axiom,(
% 1.72/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.72/0.60  fof(f618,plain,(
% 1.72/0.60    ~spl3_17 | spl3_2 | ~spl3_14),
% 1.72/0.60    inference(avatar_split_clause,[],[f612,f521,f75,f578])).
% 1.72/0.60  fof(f612,plain,(
% 1.72/0.60    sK2 != k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) | (spl3_2 | ~spl3_14)),
% 1.72/0.60    inference(superposition,[],[f77,f523])).
% 1.72/0.60  fof(f77,plain,(
% 1.72/0.60    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl3_2),
% 1.72/0.60    inference(avatar_component_clause,[],[f75])).
% 1.72/0.60  fof(f617,plain,(
% 1.72/0.60    ~spl3_18 | spl3_3 | ~spl3_14),
% 1.72/0.60    inference(avatar_split_clause,[],[f611,f521,f79,f583])).
% 1.72/0.60  fof(f79,plain,(
% 1.72/0.60    spl3_3 <=> sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.72/0.60  fof(f611,plain,(
% 1.72/0.60    sK1 != k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) | (spl3_3 | ~spl3_14)),
% 1.72/0.60    inference(superposition,[],[f81,f523])).
% 1.72/0.60  fof(f81,plain,(
% 1.72/0.60    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | spl3_3),
% 1.72/0.60    inference(avatar_component_clause,[],[f79])).
% 1.72/0.60  fof(f524,plain,(
% 1.72/0.60    spl3_14 | ~spl3_6),
% 1.72/0.60    inference(avatar_split_clause,[],[f519,f184,f521])).
% 1.72/0.60  fof(f184,plain,(
% 1.72/0.60    spl3_6 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2))),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.72/0.60  fof(f519,plain,(
% 1.72/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK1,k5_xboole_0(sK2,k3_xboole_0(sK1,sK2))) | ~spl3_6),
% 1.72/0.60    inference(forward_demodulation,[],[f423,f125])).
% 1.72/0.60  fof(f423,plain,(
% 1.72/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k5_xboole_0(k3_xboole_0(sK1,sK2),sK1)) | ~spl3_6),
% 1.72/0.60    inference(backward_demodulation,[],[f186,f125])).
% 1.72/0.60  fof(f186,plain,(
% 1.72/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) | ~spl3_6),
% 1.72/0.60    inference(avatar_component_clause,[],[f184])).
% 1.72/0.60  fof(f187,plain,(
% 1.72/0.60    spl3_6 | ~spl3_1),
% 1.72/0.60    inference(avatar_split_clause,[],[f182,f70,f184])).
% 1.72/0.60  fof(f70,plain,(
% 1.72/0.60    spl3_1 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.72/0.60    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.72/0.60  fof(f182,plain,(
% 1.72/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k3_xboole_0(sK1,sK2),k5_xboole_0(sK1,sK2)) | ~spl3_1),
% 1.72/0.60    inference(forward_demodulation,[],[f181,f33])).
% 1.72/0.60  fof(f181,plain,(
% 1.72/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(k5_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) | ~spl3_1),
% 1.72/0.60    inference(forward_demodulation,[],[f72,f61])).
% 1.72/0.60  fof(f72,plain,(
% 1.72/0.60    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl3_1),
% 1.72/0.60    inference(avatar_component_clause,[],[f70])).
% 1.72/0.60  fof(f92,plain,(
% 1.72/0.60    ~spl3_5 | ~spl3_3),
% 1.72/0.60    inference(avatar_split_clause,[],[f59,f79,f89])).
% 1.72/0.60  fof(f59,plain,(
% 1.72/0.60    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 1.72/0.60    inference(definition_unfolding,[],[f23,f55])).
% 1.72/0.60  fof(f23,plain,(
% 1.72/0.60    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.72/0.60    inference(cnf_transformation,[],[f22])).
% 1.72/0.60  fof(f22,plain,(
% 1.72/0.60    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.72/0.60    inference(ennf_transformation,[],[f21])).
% 1.72/0.60  fof(f21,negated_conjecture,(
% 1.72/0.60    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.72/0.60    inference(negated_conjecture,[],[f20])).
% 1.72/0.60  fof(f20,conjecture,(
% 1.72/0.60    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.72/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.72/0.60  fof(f87,plain,(
% 1.72/0.60    ~spl3_2 | ~spl3_4),
% 1.72/0.60    inference(avatar_split_clause,[],[f58,f84,f75])).
% 1.72/0.60  fof(f58,plain,(
% 1.72/0.60    k1_xboole_0 != sK1 | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.72/0.60    inference(definition_unfolding,[],[f24,f55])).
% 1.72/0.60  fof(f24,plain,(
% 1.72/0.60    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 1.72/0.60    inference(cnf_transformation,[],[f22])).
% 1.72/0.60  fof(f82,plain,(
% 1.72/0.60    ~spl3_2 | ~spl3_3),
% 1.72/0.60    inference(avatar_split_clause,[],[f57,f79,f75])).
% 1.72/0.60  fof(f57,plain,(
% 1.72/0.60    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 1.72/0.60    inference(definition_unfolding,[],[f25,f55,f55])).
% 1.72/0.61  fof(f25,plain,(
% 1.72/0.61    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 1.72/0.61    inference(cnf_transformation,[],[f22])).
% 1.72/0.61  fof(f73,plain,(
% 1.72/0.61    spl3_1),
% 1.72/0.61    inference(avatar_split_clause,[],[f56,f70])).
% 1.72/0.61  fof(f56,plain,(
% 1.72/0.61    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 1.72/0.61    inference(definition_unfolding,[],[f26,f55,f54])).
% 1.72/0.61  fof(f26,plain,(
% 1.72/0.61    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.72/0.61    inference(cnf_transformation,[],[f22])).
% 1.72/0.61  % SZS output end Proof for theBenchmark
% 1.72/0.61  % (20381)------------------------------
% 1.72/0.61  % (20381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.61  % (20381)Termination reason: Refutation
% 1.72/0.61  
% 1.72/0.61  % (20381)Memory used [KB]: 11769
% 1.72/0.61  % (20381)Time elapsed: 0.160 s
% 1.72/0.61  % (20381)------------------------------
% 1.72/0.61  % (20381)------------------------------
% 1.72/0.61  % (20364)Success in time 0.246 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:00 EST 2020

% Result     : Theorem 3.24s
% Output     : Refutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 681 expanded)
%              Number of leaves         :   30 ( 235 expanded)
%              Depth                    :   19
%              Number of atoms          :  178 ( 766 expanded)
%              Number of equality atoms :   61 ( 601 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2523,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f87,f92,f220,f1041,f1427,f2456,f2518])).

fof(f2518,plain,
    ( spl3_1
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f2508])).

fof(f2508,plain,
    ( $false
    | spl3_1
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f183,f142,f2455,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f2455,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f2453])).

fof(f2453,plain,
    ( spl3_9
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f142,plain,
    ( ! [X0] : ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0),sK2)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f86,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f50,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f46,f64])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f56,f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f86,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f183,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(forward_demodulation,[],[f182,f146])).

fof(f146,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f144,f42])).

fof(f42,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f144,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f143,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f143,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f72,f73])).

fof(f73,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f40,f67])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f43,f66])).

fof(f43,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f39,f68])).

fof(f68,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f45,f67])).

fof(f45,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f182,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f173,f37])).

fof(f173,plain,(
    ! [X0] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,X0)),X0) ),
    inference(superposition,[],[f167,f73])).

fof(f167,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(forward_demodulation,[],[f74,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f74,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f41,f68])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f2456,plain,
    ( spl3_9
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f2451,f1424,f2453])).

fof(f1424,plain,
    ( spl3_7
  <=> r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f2451,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f2450,f144])).

fof(f2450,plain,
    ( r1_tarski(k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f2449,f42])).

fof(f2449,plain,
    ( r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k1_xboole_0),sK2)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f2448,f37])).

fof(f2448,plain,
    ( r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f2420,f98])).

fof(f98,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f47,f42])).

fof(f2420,plain,
    ( r1_tarski(k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2)
    | ~ spl3_7 ),
    inference(superposition,[],[f1486,f73])).

fof(f1486,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(X0,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0)))))),sK2)
    | ~ spl3_7 ),
    inference(forward_demodulation,[],[f1468,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] : k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) ),
    inference(definition_unfolding,[],[f48,f67,f67,f67,f67])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1468,plain,
    ( ! [X0] : r1_tarski(k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(X0,k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X0)))),sK2)
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f167,f1426,f49])).

fof(f1426,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f1424])).

fof(f1427,plain,
    ( spl3_7
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f1321,f1038,f1424])).

fof(f1038,plain,
    ( spl3_5
  <=> r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f1321,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f1040,f288])).

fof(f288,plain,(
    ! [X6,X10,X8,X7,X11,X9] : k6_enumset1(X6,X6,X6,X7,X8,X9,X10,X11) = k6_enumset1(X6,X6,X7,X8,X9,X10,X11,X11) ),
    inference(superposition,[],[f82,f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6))) ),
    inference(definition_unfolding,[],[f58,f57,f67,f63,f66])).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7))) ),
    inference(definition_unfolding,[],[f61,f67,f57,f69])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f38,f66])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f61,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).

fof(f1040,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f1038])).

fof(f1041,plain,
    ( spl3_5
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f985,f217,f1038])).

fof(f217,plain,
    ( spl3_3
  <=> r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f985,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f219,f255])).

fof(f255,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X5,X6) ),
    inference(superposition,[],[f80,f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f59,f67,f63,f65])).

fof(f59,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

fof(f219,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f217])).

fof(f220,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f215,f89,f217])).

fof(f89,plain,
    ( spl3_2
  <=> r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f215,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f214,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X3,X0,X2) ),
    inference(definition_unfolding,[],[f53,f64,f64])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).

fof(f214,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f91,f79])).

fof(f91,plain,
    ( r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f89])).

fof(f92,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f71,f89])).

fof(f71,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f35,f67,f66])).

fof(f35,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f87,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f36,f84])).

fof(f36,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (3652)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.46  % (3645)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (3649)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (3644)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (3655)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (3642)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (3647)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (3650)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (3651)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (3646)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (3658)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (3643)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (3657)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.50  % (3654)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (3641)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.51  % (3648)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.51  % (3656)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.52  % (3653)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 3.24/0.78  % (3647)Refutation found. Thanks to Tanya!
% 3.24/0.78  % SZS status Theorem for theBenchmark
% 3.24/0.78  % SZS output start Proof for theBenchmark
% 3.24/0.78  fof(f2523,plain,(
% 3.24/0.78    $false),
% 3.24/0.78    inference(avatar_sat_refutation,[],[f87,f92,f220,f1041,f1427,f2456,f2518])).
% 3.24/0.78  fof(f2518,plain,(
% 3.24/0.78    spl3_1 | ~spl3_9),
% 3.24/0.78    inference(avatar_contradiction_clause,[],[f2508])).
% 3.24/0.78  fof(f2508,plain,(
% 3.24/0.78    $false | (spl3_1 | ~spl3_9)),
% 3.24/0.78    inference(unit_resulting_resolution,[],[f183,f142,f2455,f49])).
% 3.24/0.78  fof(f49,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f30])).
% 3.24/0.78  fof(f30,plain,(
% 3.24/0.78    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.24/0.78    inference(flattening,[],[f29])).
% 3.24/0.78  fof(f29,plain,(
% 3.24/0.78    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.24/0.78    inference(ennf_transformation,[],[f5])).
% 3.24/0.78  fof(f5,axiom,(
% 3.24/0.78    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.24/0.78  fof(f2455,plain,(
% 3.24/0.78    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~spl3_9),
% 3.24/0.78    inference(avatar_component_clause,[],[f2453])).
% 3.24/0.78  fof(f2453,plain,(
% 3.24/0.78    spl3_9 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 3.24/0.78    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 3.24/0.78  fof(f142,plain,(
% 3.24/0.78    ( ! [X0] : (~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,X0),sK2)) ) | spl3_1),
% 3.24/0.78    inference(unit_resulting_resolution,[],[f86,f78])).
% 3.24/0.78  fof(f78,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f50,f66])).
% 3.24/0.78  fof(f66,plain,(
% 3.24/0.78    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f44,f65])).
% 3.24/0.78  fof(f65,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f46,f64])).
% 3.24/0.78  fof(f64,plain,(
% 3.24/0.78    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f54,f63])).
% 3.24/0.78  fof(f63,plain,(
% 3.24/0.78    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f55,f62])).
% 3.24/0.78  fof(f62,plain,(
% 3.24/0.78    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f56,f57])).
% 3.24/0.78  fof(f57,plain,(
% 3.24/0.78    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f21])).
% 3.24/0.78  fof(f21,axiom,(
% 3.24/0.78    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 3.24/0.78  fof(f56,plain,(
% 3.24/0.78    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f20])).
% 3.24/0.78  fof(f20,axiom,(
% 3.24/0.78    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 3.24/0.78  fof(f55,plain,(
% 3.24/0.78    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f19])).
% 3.24/0.78  fof(f19,axiom,(
% 3.24/0.78    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 3.24/0.78  fof(f54,plain,(
% 3.24/0.78    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f18])).
% 3.24/0.78  fof(f18,axiom,(
% 3.24/0.78    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 3.24/0.78  fof(f46,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f17])).
% 3.24/0.78  fof(f17,axiom,(
% 3.24/0.78    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 3.24/0.78  fof(f44,plain,(
% 3.24/0.78    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f16])).
% 3.24/0.78  fof(f16,axiom,(
% 3.24/0.78    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 3.24/0.78  fof(f50,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f34])).
% 3.24/0.78  fof(f34,plain,(
% 3.24/0.78    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.24/0.78    inference(flattening,[],[f33])).
% 3.24/0.78  fof(f33,plain,(
% 3.24/0.78    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 3.24/0.78    inference(nnf_transformation,[],[f23])).
% 3.24/0.78  fof(f23,axiom,(
% 3.24/0.78    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 3.24/0.78  fof(f86,plain,(
% 3.24/0.78    ~r2_hidden(sK0,sK2) | spl3_1),
% 3.24/0.78    inference(avatar_component_clause,[],[f84])).
% 3.24/0.78  fof(f84,plain,(
% 3.24/0.78    spl3_1 <=> r2_hidden(sK0,sK2)),
% 3.24/0.78    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.24/0.78  fof(f183,plain,(
% 3.24/0.78    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.24/0.78    inference(forward_demodulation,[],[f182,f146])).
% 3.24/0.78  fof(f146,plain,(
% 3.24/0.78    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 3.24/0.78    inference(superposition,[],[f144,f42])).
% 3.24/0.78  fof(f42,plain,(
% 3.24/0.78    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f1])).
% 3.24/0.78  fof(f1,axiom,(
% 3.24/0.78    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 3.24/0.78  fof(f144,plain,(
% 3.24/0.78    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 3.24/0.78    inference(forward_demodulation,[],[f143,f37])).
% 3.24/0.78  fof(f37,plain,(
% 3.24/0.78    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 3.24/0.78    inference(cnf_transformation,[],[f8])).
% 3.24/0.78  fof(f8,axiom,(
% 3.24/0.78    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 3.24/0.78  fof(f143,plain,(
% 3.24/0.78    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 3.24/0.78    inference(forward_demodulation,[],[f72,f73])).
% 3.24/0.78  fof(f73,plain,(
% 3.24/0.78    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 3.24/0.78    inference(definition_unfolding,[],[f40,f67])).
% 3.24/0.78  fof(f67,plain,(
% 3.24/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 3.24/0.78    inference(definition_unfolding,[],[f43,f66])).
% 3.24/0.78  fof(f43,plain,(
% 3.24/0.78    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 3.24/0.78    inference(cnf_transformation,[],[f22])).
% 3.24/0.78  fof(f22,axiom,(
% 3.24/0.78    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 3.24/0.78  fof(f40,plain,(
% 3.24/0.78    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 3.24/0.78    inference(cnf_transformation,[],[f27])).
% 3.24/0.78  fof(f27,plain,(
% 3.24/0.78    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 3.24/0.78    inference(rectify,[],[f2])).
% 3.24/0.78  fof(f2,axiom,(
% 3.24/0.78    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 3.24/0.78  fof(f72,plain,(
% 3.24/0.78    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 3.24/0.78    inference(definition_unfolding,[],[f39,f68])).
% 3.24/0.78  fof(f68,plain,(
% 3.24/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 3.24/0.78    inference(definition_unfolding,[],[f45,f67])).
% 3.24/0.78  fof(f45,plain,(
% 3.24/0.78    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 3.24/0.78    inference(cnf_transformation,[],[f9])).
% 3.24/0.78  fof(f9,axiom,(
% 3.24/0.78    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 3.24/0.78  fof(f39,plain,(
% 3.24/0.78    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.24/0.78    inference(cnf_transformation,[],[f26])).
% 3.24/0.78  fof(f26,plain,(
% 3.24/0.78    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.24/0.78    inference(rectify,[],[f3])).
% 3.24/0.78  fof(f3,axiom,(
% 3.24/0.78    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.24/0.78  fof(f182,plain,(
% 3.24/0.78    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 3.24/0.78    inference(forward_demodulation,[],[f173,f37])).
% 3.24/0.78  fof(f173,plain,(
% 3.24/0.78    ( ! [X0] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,X0)),X0)) )),
% 3.24/0.78    inference(superposition,[],[f167,f73])).
% 3.24/0.78  fof(f167,plain,(
% 3.24/0.78    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 3.24/0.78    inference(forward_demodulation,[],[f74,f47])).
% 3.24/0.78  fof(f47,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 3.24/0.78    inference(cnf_transformation,[],[f7])).
% 3.24/0.78  fof(f7,axiom,(
% 3.24/0.78    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 3.24/0.78  fof(f74,plain,(
% 3.24/0.78    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f41,f68])).
% 3.24/0.78  fof(f41,plain,(
% 3.24/0.78    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f4])).
% 3.24/0.78  fof(f4,axiom,(
% 3.24/0.78    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 3.24/0.78  fof(f2456,plain,(
% 3.24/0.78    spl3_9 | ~spl3_7),
% 3.24/0.78    inference(avatar_split_clause,[],[f2451,f1424,f2453])).
% 3.24/0.78  fof(f1424,plain,(
% 3.24/0.78    spl3_7 <=> r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 3.24/0.78    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 3.24/0.78  fof(f2451,plain,(
% 3.24/0.78    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~spl3_7),
% 3.24/0.78    inference(forward_demodulation,[],[f2450,f144])).
% 3.24/0.78  fof(f2450,plain,(
% 3.24/0.78    r1_tarski(k5_xboole_0(k1_xboole_0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),sK2) | ~spl3_7),
% 3.24/0.78    inference(forward_demodulation,[],[f2449,f42])).
% 3.24/0.78  fof(f2449,plain,(
% 3.24/0.78    r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k1_xboole_0),sK2) | ~spl3_7),
% 3.24/0.78    inference(forward_demodulation,[],[f2448,f37])).
% 3.24/0.78  fof(f2448,plain,(
% 3.24/0.78    r1_tarski(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2) | ~spl3_7),
% 3.24/0.78    inference(forward_demodulation,[],[f2420,f98])).
% 3.24/0.78  fof(f98,plain,(
% 3.24/0.78    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 3.24/0.78    inference(superposition,[],[f47,f42])).
% 3.24/0.78  fof(f2420,plain,(
% 3.24/0.78    r1_tarski(k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),sK2) | ~spl3_7),
% 3.24/0.78    inference(superposition,[],[f1486,f73])).
% 3.24/0.78  fof(f1486,plain,(
% 3.24/0.78    ( ! [X0] : (r1_tarski(k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(X0,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),X0)))))),sK2)) ) | ~spl3_7),
% 3.24/0.78    inference(forward_demodulation,[],[f1468,f75])).
% 3.24/0.78  fof(f75,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)),X2)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))))) )),
% 3.24/0.78    inference(definition_unfolding,[],[f48,f67,f67,f67,f67])).
% 3.24/0.78  fof(f48,plain,(
% 3.24/0.78    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.24/0.78    inference(cnf_transformation,[],[f6])).
% 3.24/0.78  fof(f6,axiom,(
% 3.24/0.78    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 3.24/0.78  fof(f1468,plain,(
% 3.24/0.78    ( ! [X0] : (r1_tarski(k5_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(X0,k3_tarski(k6_enumset1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),X0)))),sK2)) ) | ~spl3_7),
% 3.24/0.78    inference(unit_resulting_resolution,[],[f167,f1426,f49])).
% 3.24/0.78  fof(f1426,plain,(
% 3.24/0.78    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) | ~spl3_7),
% 3.24/0.78    inference(avatar_component_clause,[],[f1424])).
% 3.24/0.78  fof(f1427,plain,(
% 3.24/0.78    spl3_7 | ~spl3_5),
% 3.24/0.78    inference(avatar_split_clause,[],[f1321,f1038,f1424])).
% 3.24/0.78  fof(f1038,plain,(
% 3.24/0.78    spl3_5 <=> r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 3.24/0.78    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 3.24/0.78  fof(f1321,plain,(
% 3.24/0.78    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) | ~spl3_5),
% 3.24/0.78    inference(backward_demodulation,[],[f1040,f288])).
% 3.24/0.78  fof(f288,plain,(
% 3.24/0.78    ( ! [X6,X10,X8,X7,X11,X9] : (k6_enumset1(X6,X6,X6,X7,X8,X9,X10,X11) = k6_enumset1(X6,X6,X7,X8,X9,X10,X11,X11)) )),
% 3.24/0.78    inference(superposition,[],[f82,f80])).
% 3.24/0.78  fof(f80,plain,(
% 3.24/0.78    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X6)))) )),
% 3.24/0.78    inference(definition_unfolding,[],[f58,f57,f67,f63,f66])).
% 3.24/0.78  fof(f58,plain,(
% 3.24/0.78    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))) )),
% 3.24/0.78    inference(cnf_transformation,[],[f11])).
% 3.24/0.78  fof(f11,axiom,(
% 3.24/0.78    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k2_tarski(X5,X6))),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_enumset1)).
% 3.24/0.78  fof(f82,plain,(
% 3.24/0.78    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6),k6_enumset1(X7,X7,X7,X7,X7,X7,X7,X7)))) )),
% 3.24/0.78    inference(definition_unfolding,[],[f61,f67,f57,f69])).
% 3.24/0.78  fof(f69,plain,(
% 3.24/0.78    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f38,f66])).
% 3.24/0.78  fof(f38,plain,(
% 3.24/0.78    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f15])).
% 3.24/0.78  fof(f15,axiom,(
% 3.24/0.78    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 3.24/0.78  fof(f61,plain,(
% 3.24/0.78    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 3.24/0.78    inference(cnf_transformation,[],[f14])).
% 3.24/0.78  fof(f14,axiom,(
% 3.24/0.78    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_enumset1)).
% 3.24/0.78  fof(f1040,plain,(
% 3.24/0.78    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) | ~spl3_5),
% 3.24/0.78    inference(avatar_component_clause,[],[f1038])).
% 3.24/0.78  fof(f1041,plain,(
% 3.24/0.78    spl3_5 | ~spl3_3),
% 3.24/0.78    inference(avatar_split_clause,[],[f985,f217,f1038])).
% 3.24/0.78  fof(f217,plain,(
% 3.24/0.78    spl3_3 <=> r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 3.24/0.78    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 3.24/0.78  fof(f985,plain,(
% 3.24/0.78    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) | ~spl3_3),
% 3.24/0.78    inference(backward_demodulation,[],[f219,f255])).
% 3.24/0.78  fof(f255,plain,(
% 3.24/0.78    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X5,X6)) )),
% 3.24/0.78    inference(superposition,[],[f80,f70])).
% 3.24/0.78  fof(f70,plain,(
% 3.24/0.78    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7)))) )),
% 3.24/0.78    inference(definition_unfolding,[],[f59,f67,f63,f65])).
% 3.24/0.78  fof(f59,plain,(
% 3.24/0.78    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 3.24/0.78    inference(cnf_transformation,[],[f12])).
% 3.24/0.78  fof(f12,axiom,(
% 3.24/0.78    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).
% 3.24/0.78  fof(f219,plain,(
% 3.24/0.78    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) | ~spl3_3),
% 3.24/0.78    inference(avatar_component_clause,[],[f217])).
% 3.24/0.78  fof(f220,plain,(
% 3.24/0.78    spl3_3 | ~spl3_2),
% 3.24/0.78    inference(avatar_split_clause,[],[f215,f89,f217])).
% 3.24/0.78  fof(f89,plain,(
% 3.24/0.78    spl3_2 <=> r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 3.24/0.78    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 3.24/0.78  fof(f215,plain,(
% 3.24/0.78    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) | ~spl3_2),
% 3.24/0.78    inference(forward_demodulation,[],[f214,f79])).
% 3.24/0.78  fof(f79,plain,(
% 3.24/0.78    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X1,X1,X1,X1,X1,X3,X0,X2)) )),
% 3.24/0.78    inference(definition_unfolding,[],[f53,f64,f64])).
% 3.24/0.78  fof(f53,plain,(
% 3.24/0.78    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)) )),
% 3.24/0.78    inference(cnf_transformation,[],[f10])).
% 3.24/0.78  fof(f10,axiom,(
% 3.24/0.78    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X1,X3,X0,X2)),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_enumset1)).
% 3.24/0.78  fof(f214,plain,(
% 3.24/0.78    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) | ~spl3_2),
% 3.24/0.78    inference(forward_demodulation,[],[f91,f79])).
% 3.24/0.78  fof(f91,plain,(
% 3.24/0.78    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) | ~spl3_2),
% 3.24/0.78    inference(avatar_component_clause,[],[f89])).
% 3.24/0.78  fof(f92,plain,(
% 3.24/0.78    spl3_2),
% 3.24/0.78    inference(avatar_split_clause,[],[f71,f89])).
% 3.24/0.78  fof(f71,plain,(
% 3.24/0.78    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 3.24/0.78    inference(definition_unfolding,[],[f35,f67,f66])).
% 3.24/0.78  fof(f35,plain,(
% 3.24/0.78    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.24/0.78    inference(cnf_transformation,[],[f32])).
% 3.24/0.78  fof(f32,plain,(
% 3.24/0.78    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 3.24/0.78    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f28,f31])).
% 3.24/0.78  fof(f31,plain,(
% 3.24/0.78    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 3.24/0.78    introduced(choice_axiom,[])).
% 3.24/0.78  fof(f28,plain,(
% 3.24/0.78    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 3.24/0.78    inference(ennf_transformation,[],[f25])).
% 3.24/0.78  fof(f25,negated_conjecture,(
% 3.24/0.78    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.24/0.78    inference(negated_conjecture,[],[f24])).
% 3.24/0.78  fof(f24,conjecture,(
% 3.24/0.78    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 3.24/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 3.24/0.78  fof(f87,plain,(
% 3.24/0.78    ~spl3_1),
% 3.24/0.78    inference(avatar_split_clause,[],[f36,f84])).
% 3.24/0.78  fof(f36,plain,(
% 3.24/0.78    ~r2_hidden(sK0,sK2)),
% 3.24/0.78    inference(cnf_transformation,[],[f32])).
% 3.24/0.78  % SZS output end Proof for theBenchmark
% 3.24/0.78  % (3647)------------------------------
% 3.24/0.78  % (3647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.24/0.78  % (3647)Termination reason: Refutation
% 3.24/0.78  
% 3.24/0.78  % (3647)Memory used [KB]: 10106
% 3.24/0.78  % (3647)Time elapsed: 0.308 s
% 3.24/0.78  % (3647)------------------------------
% 3.24/0.78  % (3647)------------------------------
% 3.24/0.79  % (3640)Success in time 0.428 s
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:20 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 337 expanded)
%              Number of leaves         :   19 ( 113 expanded)
%              Depth                    :   15
%              Number of atoms          :  207 ( 578 expanded)
%              Number of equality atoms :   83 ( 328 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5558,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f149,f150,f151,f3094,f4971,f5544])).

fof(f5544,plain,
    ( ~ spl9_1
    | ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f5543])).

fof(f5543,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f5536,f148])).

fof(f148,plain,
    ( r2_hidden(sK3,sK4)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl9_3
  <=> r2_hidden(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f5536,plain,
    ( ~ r2_hidden(sK3,sK4)
    | ~ spl9_1 ),
    inference(trivial_inequality_removal,[],[f5505])).

fof(f5505,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK3,sK4)
    | ~ spl9_1 ),
    inference(superposition,[],[f94,f5501])).

fof(f5501,plain,
    ( sK4 = k4_xboole_0(sK4,k1_tarski(sK3))
    | ~ spl9_1 ),
    inference(resolution,[],[f5497,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X1,X0,X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ~ sP1(X1,X0,X2) )
      & ( sP1(X1,X0,X2)
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> sP1(X1,X0,X2) ) ),
    inference(definition_folding,[],[f5,f41])).

fof(f41,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f5497,plain,
    ( sP1(k1_tarski(sK3),sK4,sK4)
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f5481,f4889])).

fof(f4889,plain,
    ( sK4 = k4_xboole_0(sK4,k1_tarski(sK2))
    | ~ spl9_1 ),
    inference(superposition,[],[f1441,f4777])).

fof(f4777,plain,
    ( k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK4)
    | ~ spl9_1 ),
    inference(superposition,[],[f1444,f3536])).

fof(f3536,plain,
    ( sK4 = k4_xboole_0(sK4,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f3502,f72])).

fof(f72,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f3502,plain,
    ( k4_xboole_0(sK4,k1_xboole_0) = k4_xboole_0(sK4,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))
    | ~ spl9_1 ),
    inference(superposition,[],[f124,f3182])).

fof(f3182,plain,
    ( k1_xboole_0 = k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))))
    | ~ spl9_1 ),
    inference(forward_demodulation,[],[f3146,f159])).

fof(f159,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f76,f71])).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f76,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f3146,plain,
    ( k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))) = k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))
    | ~ spl9_1 ),
    inference(superposition,[],[f122,f139])).

fof(f139,plain,
    ( k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl9_1
  <=> k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f122,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f77,f81,f81])).

fof(f81,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f124,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f83,f81])).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f1444,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = X2 ),
    inference(forward_demodulation,[],[f1443,f665])).

fof(f665,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X6,X7)) = X6 ),
    inference(superposition,[],[f123,f124])).

fof(f123,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f79,f81])).

fof(f79,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f1443,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(X2,k4_xboole_0(X2,X4)) ),
    inference(forward_demodulation,[],[f1442,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1442,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),X2) ),
    inference(forward_demodulation,[],[f1367,f72])).

fof(f1367,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),k4_xboole_0(X2,k1_xboole_0)) ),
    inference(superposition,[],[f131,f76])).

fof(f131,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f100,f81])).

fof(f100,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f1441,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f1440,f665])).

fof(f1440,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f1439,f78])).

fof(f1439,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f1366,f72])).

fof(f1366,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f131,f159])).

fof(f5481,plain,
    ( sP1(k1_tarski(sK3),k4_xboole_0(sK4,k1_tarski(sK2)),sK4)
    | ~ spl9_1 ),
    inference(superposition,[],[f530,f3536])).

fof(f530,plain,(
    ! [X14,X15,X16] : sP1(X16,k4_xboole_0(X14,X15),k4_xboole_0(X14,k2_xboole_0(X15,X16))) ),
    inference(superposition,[],[f136,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f136,plain,(
    ! [X0,X1] : sP1(X1,X0,k4_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f4971,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_contradiction_clause,[],[f4970])).

fof(f4970,plain,
    ( $false
    | ~ spl9_1
    | ~ spl9_2 ),
    inference(subsumption_resolution,[],[f4968,f144])).

fof(f144,plain,
    ( r2_hidden(sK2,sK4)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl9_2
  <=> r2_hidden(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f4968,plain,
    ( ~ r2_hidden(sK2,sK4)
    | ~ spl9_1 ),
    inference(trivial_inequality_removal,[],[f4939])).

fof(f4939,plain,
    ( sK4 != sK4
    | ~ r2_hidden(sK2,sK4)
    | ~ spl9_1 ),
    inference(superposition,[],[f94,f4889])).

fof(f3094,plain,
    ( spl9_1
    | spl9_2
    | spl9_3 ),
    inference(avatar_contradiction_clause,[],[f3093])).

fof(f3093,plain,
    ( $false
    | spl9_1
    | spl9_2
    | spl9_3 ),
    inference(subsumption_resolution,[],[f3081,f140])).

fof(f140,plain,
    ( k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f138])).

fof(f3081,plain,
    ( k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4)
    | spl9_2
    | spl9_3 ),
    inference(superposition,[],[f1441,f2956])).

fof(f2956,plain,
    ( sK4 = k4_xboole_0(sK4,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))
    | spl9_2
    | spl9_3 ),
    inference(resolution,[],[f2890,f116])).

fof(f2890,plain,
    ( sP1(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4,sK4)
    | spl9_2
    | spl9_3 ),
    inference(superposition,[],[f2850,f252])).

fof(f252,plain,
    ( sK4 = k4_xboole_0(sK4,k1_tarski(sK3))
    | spl9_3 ),
    inference(resolution,[],[f95,f147])).

fof(f147,plain,
    ( ~ r2_hidden(sK3,sK4)
    | spl9_3 ),
    inference(avatar_component_clause,[],[f146])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f2850,plain,
    ( ! [X32] : sP1(k2_xboole_0(k1_tarski(sK2),X32),sK4,k4_xboole_0(sK4,X32))
    | spl9_2 ),
    inference(superposition,[],[f136,f518])).

fof(f518,plain,
    ( ! [X23] : k4_xboole_0(sK4,k2_xboole_0(k1_tarski(sK2),X23)) = k4_xboole_0(sK4,X23)
    | spl9_2 ),
    inference(superposition,[],[f97,f251])).

fof(f251,plain,
    ( sK4 = k4_xboole_0(sK4,k1_tarski(sK2))
    | spl9_2 ),
    inference(resolution,[],[f95,f143])).

fof(f143,plain,
    ( ~ r2_hidden(sK2,sK4)
    | spl9_2 ),
    inference(avatar_component_clause,[],[f142])).

fof(f151,plain,
    ( spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f119,f142,f138])).

fof(f119,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4) ),
    inference(definition_unfolding,[],[f66,f80,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

fof(f66,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( ( r2_hidden(sK3,sK4)
      | r2_hidden(sK2,sK4)
      | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4) )
    & ( ( ~ r2_hidden(sK3,sK4)
        & ~ r2_hidden(sK2,sK4) )
      | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f44,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK3,sK4)
        | r2_hidden(sK2,sK4)
        | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4) )
      & ( ( ~ r2_hidden(sK3,sK4)
          & ~ r2_hidden(sK2,sK4) )
        | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f150,plain,
    ( spl9_1
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f118,f146,f138])).

fof(f118,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4) ),
    inference(definition_unfolding,[],[f67,f80,f80])).

fof(f67,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f46])).

fof(f149,plain,
    ( ~ spl9_1
    | spl9_2
    | spl9_3 ),
    inference(avatar_split_clause,[],[f117,f146,f142,f138])).

fof(f117,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4) ),
    inference(definition_unfolding,[],[f68,f80,f80])).

fof(f68,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:21:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.43/0.56  % (9425)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.58  % (9442)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.73/0.58  % (9434)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.73/0.59  % (9426)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.73/0.59  % (9440)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.73/0.59  % (9420)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.73/0.60  % (9424)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.73/0.60  % (9429)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.73/0.60  % (9432)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.73/0.60  % (9419)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.73/0.60  % (9423)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.73/0.61  % (9439)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.73/0.61  % (9441)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.73/0.61  % (9433)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.73/0.61  % (9438)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.73/0.62  % (9431)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.73/0.62  % (9435)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.73/0.62  % (9422)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.73/0.62  % (9446)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.73/0.62  % (9435)Refutation not found, incomplete strategy% (9435)------------------------------
% 1.73/0.62  % (9435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.62  % (9435)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.62  
% 1.73/0.62  % (9435)Memory used [KB]: 10746
% 1.73/0.62  % (9435)Time elapsed: 0.187 s
% 1.73/0.62  % (9435)------------------------------
% 1.73/0.62  % (9435)------------------------------
% 1.73/0.62  % (9429)Refutation not found, incomplete strategy% (9429)------------------------------
% 1.73/0.62  % (9429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.62  % (9429)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.62  
% 1.73/0.62  % (9429)Memory used [KB]: 10746
% 1.73/0.62  % (9429)Time elapsed: 0.192 s
% 1.73/0.62  % (9429)------------------------------
% 1.73/0.62  % (9429)------------------------------
% 1.73/0.62  % (9430)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.73/0.62  % (9448)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.73/0.62  % (9421)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.73/0.63  % (9443)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.73/0.63  % (9445)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.73/0.63  % (9428)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.73/0.63  % (9427)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.73/0.63  % (9437)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.73/0.63  % (9447)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.73/0.64  % (9447)Refutation not found, incomplete strategy% (9447)------------------------------
% 1.73/0.64  % (9447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.64  % (9447)Termination reason: Refutation not found, incomplete strategy
% 1.73/0.64  
% 1.73/0.64  % (9447)Memory used [KB]: 10746
% 1.73/0.64  % (9447)Time elapsed: 0.197 s
% 1.73/0.64  % (9447)------------------------------
% 1.73/0.64  % (9447)------------------------------
% 1.73/0.64  % (9436)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.73/0.64  % (9444)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 2.72/0.73  % (9479)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.72/0.73  % (9481)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.72/0.76  % (9422)Refutation not found, incomplete strategy% (9422)------------------------------
% 2.72/0.76  % (9422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.72/0.76  % (9422)Termination reason: Refutation not found, incomplete strategy
% 2.72/0.76  
% 2.72/0.76  % (9422)Memory used [KB]: 6140
% 2.72/0.76  % (9422)Time elapsed: 0.325 s
% 2.72/0.76  % (9422)------------------------------
% 2.72/0.76  % (9422)------------------------------
% 2.72/0.80  % (9496)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.72/0.80  % (9425)Refutation found. Thanks to Tanya!
% 2.72/0.80  % SZS status Theorem for theBenchmark
% 3.29/0.81  % SZS output start Proof for theBenchmark
% 3.29/0.81  fof(f5558,plain,(
% 3.29/0.81    $false),
% 3.29/0.81    inference(avatar_sat_refutation,[],[f149,f150,f151,f3094,f4971,f5544])).
% 3.29/0.81  fof(f5544,plain,(
% 3.29/0.81    ~spl9_1 | ~spl9_3),
% 3.29/0.81    inference(avatar_contradiction_clause,[],[f5543])).
% 3.29/0.81  fof(f5543,plain,(
% 3.29/0.81    $false | (~spl9_1 | ~spl9_3)),
% 3.29/0.81    inference(subsumption_resolution,[],[f5536,f148])).
% 3.29/0.81  fof(f148,plain,(
% 3.29/0.81    r2_hidden(sK3,sK4) | ~spl9_3),
% 3.29/0.81    inference(avatar_component_clause,[],[f146])).
% 3.29/0.81  fof(f146,plain,(
% 3.29/0.81    spl9_3 <=> r2_hidden(sK3,sK4)),
% 3.29/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 3.29/0.81  fof(f5536,plain,(
% 3.29/0.81    ~r2_hidden(sK3,sK4) | ~spl9_1),
% 3.29/0.81    inference(trivial_inequality_removal,[],[f5505])).
% 3.29/0.81  fof(f5505,plain,(
% 3.29/0.81    sK4 != sK4 | ~r2_hidden(sK3,sK4) | ~spl9_1),
% 3.29/0.81    inference(superposition,[],[f94,f5501])).
% 3.29/0.81  fof(f5501,plain,(
% 3.29/0.81    sK4 = k4_xboole_0(sK4,k1_tarski(sK3)) | ~spl9_1),
% 3.29/0.81    inference(resolution,[],[f5497,f116])).
% 3.29/0.81  fof(f116,plain,(
% 3.29/0.81    ( ! [X2,X0,X1] : (~sP1(X1,X0,X2) | k4_xboole_0(X0,X1) = X2) )),
% 3.29/0.81    inference(cnf_transformation,[],[f65])).
% 3.29/0.81  fof(f65,plain,(
% 3.29/0.81    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k4_xboole_0(X0,X1) != X2))),
% 3.29/0.81    inference(nnf_transformation,[],[f42])).
% 3.29/0.81  fof(f42,plain,(
% 3.29/0.81    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> sP1(X1,X0,X2))),
% 3.29/0.81    inference(definition_folding,[],[f5,f41])).
% 3.29/0.81  fof(f41,plain,(
% 3.29/0.81    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.29/0.81    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.29/0.81  fof(f5,axiom,(
% 3.29/0.81    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.29/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 3.29/0.81  fof(f5497,plain,(
% 3.29/0.81    sP1(k1_tarski(sK3),sK4,sK4) | ~spl9_1),
% 3.29/0.81    inference(forward_demodulation,[],[f5481,f4889])).
% 3.29/0.81  fof(f4889,plain,(
% 3.29/0.81    sK4 = k4_xboole_0(sK4,k1_tarski(sK2)) | ~spl9_1),
% 3.29/0.81    inference(superposition,[],[f1441,f4777])).
% 3.29/0.81  fof(f4777,plain,(
% 3.29/0.81    k1_tarski(sK2) = k4_xboole_0(k1_tarski(sK2),sK4) | ~spl9_1),
% 3.29/0.81    inference(superposition,[],[f1444,f3536])).
% 3.29/0.81  fof(f3536,plain,(
% 3.29/0.81    sK4 = k4_xboole_0(sK4,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) | ~spl9_1),
% 3.29/0.81    inference(forward_demodulation,[],[f3502,f72])).
% 3.29/0.81  fof(f72,plain,(
% 3.29/0.81    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.29/0.81    inference(cnf_transformation,[],[f13])).
% 3.29/0.81  fof(f13,axiom,(
% 3.29/0.81    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.29/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 3.29/0.81  fof(f3502,plain,(
% 3.29/0.81    k4_xboole_0(sK4,k1_xboole_0) = k4_xboole_0(sK4,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) | ~spl9_1),
% 3.29/0.81    inference(superposition,[],[f124,f3182])).
% 3.29/0.81  fof(f3182,plain,(
% 3.29/0.81    k1_xboole_0 = k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))) | ~spl9_1),
% 3.29/0.81    inference(forward_demodulation,[],[f3146,f159])).
% 3.29/0.81  fof(f159,plain,(
% 3.29/0.81    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 3.29/0.81    inference(superposition,[],[f76,f71])).
% 3.29/0.81  fof(f71,plain,(
% 3.29/0.81    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.29/0.81    inference(cnf_transformation,[],[f8])).
% 3.29/0.81  fof(f8,axiom,(
% 3.29/0.81    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 3.29/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 3.29/0.81  fof(f76,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 3.29/0.81    inference(cnf_transformation,[],[f16])).
% 3.29/0.81  fof(f16,axiom,(
% 3.29/0.81    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 3.29/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 3.29/0.81  fof(f3146,plain,(
% 3.29/0.81    k4_xboole_0(sK4,k4_xboole_0(sK4,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)))) = k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) | ~spl9_1),
% 3.29/0.81    inference(superposition,[],[f122,f139])).
% 3.29/0.81  fof(f139,plain,(
% 3.29/0.81    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4) | ~spl9_1),
% 3.29/0.81    inference(avatar_component_clause,[],[f138])).
% 3.29/0.81  fof(f138,plain,(
% 3.29/0.81    spl9_1 <=> k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4)),
% 3.29/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 3.29/0.81  fof(f122,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 3.29/0.81    inference(definition_unfolding,[],[f77,f81,f81])).
% 3.29/0.81  fof(f81,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.29/0.81    inference(cnf_transformation,[],[f18])).
% 3.29/0.81  fof(f18,axiom,(
% 3.29/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.29/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.29/0.81  fof(f77,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.29/0.81    inference(cnf_transformation,[],[f3])).
% 3.29/0.81  fof(f3,axiom,(
% 3.29/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.29/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.29/0.81  fof(f124,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.29/0.81    inference(definition_unfolding,[],[f83,f81])).
% 3.29/0.81  fof(f83,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.29/0.81    inference(cnf_transformation,[],[f17])).
% 3.29/0.81  fof(f17,axiom,(
% 3.29/0.81    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.29/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 3.29/0.81  fof(f1444,plain,(
% 3.29/0.81    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = X2) )),
% 3.29/0.81    inference(forward_demodulation,[],[f1443,f665])).
% 3.29/0.81  fof(f665,plain,(
% 3.29/0.81    ( ! [X6,X7] : (k2_xboole_0(X6,k4_xboole_0(X6,X7)) = X6) )),
% 3.29/0.81    inference(superposition,[],[f123,f124])).
% 3.29/0.81  fof(f123,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 3.29/0.81    inference(definition_unfolding,[],[f79,f81])).
% 3.29/0.81  fof(f79,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 3.29/0.81    inference(cnf_transformation,[],[f9])).
% 3.29/0.81  fof(f9,axiom,(
% 3.29/0.81    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 3.29/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 3.29/0.81  fof(f1443,plain,(
% 3.29/0.81    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(X2,k4_xboole_0(X2,X4))) )),
% 3.29/0.81    inference(forward_demodulation,[],[f1442,f78])).
% 3.29/0.81  fof(f78,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.29/0.81    inference(cnf_transformation,[],[f2])).
% 3.29/0.81  fof(f2,axiom,(
% 3.29/0.81    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.29/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.29/0.81  fof(f1442,plain,(
% 3.29/0.81    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),X2)) )),
% 3.29/0.81    inference(forward_demodulation,[],[f1367,f72])).
% 3.29/0.81  fof(f1367,plain,(
% 3.29/0.81    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X4,k2_xboole_0(X2,X3))) = k2_xboole_0(k4_xboole_0(X2,X4),k4_xboole_0(X2,k1_xboole_0))) )),
% 3.29/0.81    inference(superposition,[],[f131,f76])).
% 3.29/0.81  fof(f131,plain,(
% 3.29/0.81    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 3.29/0.81    inference(definition_unfolding,[],[f100,f81])).
% 3.29/0.81  fof(f100,plain,(
% 3.29/0.81    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 3.29/0.81    inference(cnf_transformation,[],[f22])).
% 3.29/0.81  fof(f22,axiom,(
% 3.29/0.81    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 3.29/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 3.29/0.81  fof(f1441,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 3.29/0.81    inference(forward_demodulation,[],[f1440,f665])).
% 3.29/0.81  fof(f1440,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.29/0.81    inference(forward_demodulation,[],[f1439,f78])).
% 3.29/0.81  fof(f1439,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 3.29/0.81    inference(forward_demodulation,[],[f1366,f72])).
% 3.29/0.81  fof(f1366,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k1_xboole_0))) )),
% 3.29/0.81    inference(superposition,[],[f131,f159])).
% 3.29/0.81  fof(f5481,plain,(
% 3.29/0.81    sP1(k1_tarski(sK3),k4_xboole_0(sK4,k1_tarski(sK2)),sK4) | ~spl9_1),
% 3.29/0.81    inference(superposition,[],[f530,f3536])).
% 3.29/0.81  fof(f530,plain,(
% 3.29/0.81    ( ! [X14,X15,X16] : (sP1(X16,k4_xboole_0(X14,X15),k4_xboole_0(X14,k2_xboole_0(X15,X16)))) )),
% 3.29/0.81    inference(superposition,[],[f136,f97])).
% 3.29/0.81  fof(f97,plain,(
% 3.29/0.81    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 3.29/0.81    inference(cnf_transformation,[],[f15])).
% 3.29/0.81  fof(f15,axiom,(
% 3.29/0.81    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 3.29/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 3.29/0.81  fof(f136,plain,(
% 3.29/0.81    ( ! [X0,X1] : (sP1(X1,X0,k4_xboole_0(X0,X1))) )),
% 3.29/0.81    inference(equality_resolution,[],[f115])).
% 3.29/0.81  fof(f115,plain,(
% 3.29/0.81    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | k4_xboole_0(X0,X1) != X2) )),
% 3.29/0.81    inference(cnf_transformation,[],[f65])).
% 3.29/0.81  fof(f94,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 3.29/0.81    inference(cnf_transformation,[],[f53])).
% 3.29/0.81  fof(f53,plain,(
% 3.29/0.81    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.29/0.81    inference(nnf_transformation,[],[f30])).
% 3.29/0.81  fof(f30,axiom,(
% 3.29/0.81    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.29/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 3.29/0.81  fof(f4971,plain,(
% 3.29/0.81    ~spl9_1 | ~spl9_2),
% 3.29/0.81    inference(avatar_contradiction_clause,[],[f4970])).
% 3.29/0.81  fof(f4970,plain,(
% 3.29/0.81    $false | (~spl9_1 | ~spl9_2)),
% 3.29/0.81    inference(subsumption_resolution,[],[f4968,f144])).
% 3.29/0.81  fof(f144,plain,(
% 3.29/0.81    r2_hidden(sK2,sK4) | ~spl9_2),
% 3.29/0.81    inference(avatar_component_clause,[],[f142])).
% 3.29/0.81  fof(f142,plain,(
% 3.29/0.81    spl9_2 <=> r2_hidden(sK2,sK4)),
% 3.29/0.81    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 3.29/0.81  fof(f4968,plain,(
% 3.29/0.81    ~r2_hidden(sK2,sK4) | ~spl9_1),
% 3.29/0.81    inference(trivial_inequality_removal,[],[f4939])).
% 3.29/0.81  fof(f4939,plain,(
% 3.29/0.81    sK4 != sK4 | ~r2_hidden(sK2,sK4) | ~spl9_1),
% 3.29/0.81    inference(superposition,[],[f94,f4889])).
% 3.29/0.81  fof(f3094,plain,(
% 3.29/0.81    spl9_1 | spl9_2 | spl9_3),
% 3.29/0.81    inference(avatar_contradiction_clause,[],[f3093])).
% 3.29/0.81  fof(f3093,plain,(
% 3.29/0.81    $false | (spl9_1 | spl9_2 | spl9_3)),
% 3.29/0.81    inference(subsumption_resolution,[],[f3081,f140])).
% 3.29/0.81  fof(f140,plain,(
% 3.29/0.81    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4) | spl9_1),
% 3.29/0.81    inference(avatar_component_clause,[],[f138])).
% 3.29/0.81  fof(f3081,plain,(
% 3.29/0.81    k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4) | (spl9_2 | spl9_3)),
% 3.29/0.81    inference(superposition,[],[f1441,f2956])).
% 3.29/0.81  fof(f2956,plain,(
% 3.29/0.81    sK4 = k4_xboole_0(sK4,k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3))) | (spl9_2 | spl9_3)),
% 3.29/0.81    inference(resolution,[],[f2890,f116])).
% 3.29/0.81  fof(f2890,plain,(
% 3.29/0.81    sP1(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4,sK4) | (spl9_2 | spl9_3)),
% 3.29/0.81    inference(superposition,[],[f2850,f252])).
% 3.29/0.81  fof(f252,plain,(
% 3.29/0.81    sK4 = k4_xboole_0(sK4,k1_tarski(sK3)) | spl9_3),
% 3.29/0.81    inference(resolution,[],[f95,f147])).
% 3.29/0.81  fof(f147,plain,(
% 3.29/0.81    ~r2_hidden(sK3,sK4) | spl9_3),
% 3.29/0.81    inference(avatar_component_clause,[],[f146])).
% 3.29/0.81  fof(f95,plain,(
% 3.29/0.81    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 3.29/0.81    inference(cnf_transformation,[],[f53])).
% 3.29/0.81  fof(f2850,plain,(
% 3.29/0.81    ( ! [X32] : (sP1(k2_xboole_0(k1_tarski(sK2),X32),sK4,k4_xboole_0(sK4,X32))) ) | spl9_2),
% 3.29/0.81    inference(superposition,[],[f136,f518])).
% 3.29/0.81  fof(f518,plain,(
% 3.29/0.81    ( ! [X23] : (k4_xboole_0(sK4,k2_xboole_0(k1_tarski(sK2),X23)) = k4_xboole_0(sK4,X23)) ) | spl9_2),
% 3.29/0.81    inference(superposition,[],[f97,f251])).
% 3.29/0.81  fof(f251,plain,(
% 3.29/0.81    sK4 = k4_xboole_0(sK4,k1_tarski(sK2)) | spl9_2),
% 3.29/0.81    inference(resolution,[],[f95,f143])).
% 3.29/0.81  fof(f143,plain,(
% 3.29/0.81    ~r2_hidden(sK2,sK4) | spl9_2),
% 3.29/0.81    inference(avatar_component_clause,[],[f142])).
% 3.29/0.81  fof(f151,plain,(
% 3.29/0.81    spl9_1 | ~spl9_2),
% 3.29/0.81    inference(avatar_split_clause,[],[f119,f142,f138])).
% 3.29/0.81  fof(f119,plain,(
% 3.29/0.81    ~r2_hidden(sK2,sK4) | k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4)),
% 3.29/0.81    inference(definition_unfolding,[],[f66,f80,f80])).
% 3.29/0.81  fof(f80,plain,(
% 3.29/0.81    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 3.29/0.81    inference(cnf_transformation,[],[f27])).
% 3.29/0.81  fof(f27,axiom,(
% 3.29/0.81    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 3.29/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).
% 3.29/0.81  fof(f66,plain,(
% 3.29/0.81    ~r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 3.29/0.81    inference(cnf_transformation,[],[f46])).
% 3.29/0.81  fof(f46,plain,(
% 3.29/0.81    (r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4))),
% 3.29/0.81    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f44,f45])).
% 3.29/0.81  fof(f45,plain,(
% 3.29/0.81    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)))),
% 3.29/0.81    introduced(choice_axiom,[])).
% 3.29/0.81  fof(f44,plain,(
% 3.29/0.81    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.29/0.81    inference(flattening,[],[f43])).
% 3.29/0.81  fof(f43,plain,(
% 3.29/0.81    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 3.29/0.81    inference(nnf_transformation,[],[f34])).
% 3.29/0.81  fof(f34,plain,(
% 3.29/0.81    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.29/0.81    inference(ennf_transformation,[],[f32])).
% 3.29/0.81  fof(f32,negated_conjecture,(
% 3.29/0.81    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.29/0.81    inference(negated_conjecture,[],[f31])).
% 3.29/0.81  fof(f31,conjecture,(
% 3.29/0.81    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 3.29/0.81    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 3.29/0.81  fof(f150,plain,(
% 3.29/0.81    spl9_1 | ~spl9_3),
% 3.29/0.81    inference(avatar_split_clause,[],[f118,f146,f138])).
% 3.29/0.81  fof(f118,plain,(
% 3.29/0.81    ~r2_hidden(sK3,sK4) | k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) = k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4)),
% 3.29/0.81    inference(definition_unfolding,[],[f67,f80,f80])).
% 3.29/0.81  fof(f67,plain,(
% 3.29/0.81    ~r2_hidden(sK3,sK4) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 3.29/0.81    inference(cnf_transformation,[],[f46])).
% 3.29/0.81  fof(f149,plain,(
% 3.29/0.81    ~spl9_1 | spl9_2 | spl9_3),
% 3.29/0.81    inference(avatar_split_clause,[],[f117,f146,f142,f138])).
% 3.29/0.81  fof(f117,plain,(
% 3.29/0.81    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)) != k4_xboole_0(k2_xboole_0(k1_tarski(sK2),k1_tarski(sK3)),sK4)),
% 3.29/0.81    inference(definition_unfolding,[],[f68,f80,f80])).
% 3.29/0.81  fof(f68,plain,(
% 3.29/0.81    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 3.29/0.81    inference(cnf_transformation,[],[f46])).
% 3.29/0.81  % SZS output end Proof for theBenchmark
% 3.29/0.81  % (9425)------------------------------
% 3.29/0.81  % (9425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.29/0.81  % (9425)Termination reason: Refutation
% 3.29/0.81  
% 3.29/0.81  % (9425)Memory used [KB]: 14072
% 3.29/0.81  % (9425)Time elapsed: 0.353 s
% 3.29/0.81  % (9425)------------------------------
% 3.29/0.81  % (9425)------------------------------
% 3.29/0.82  % (9418)Success in time 0.453 s
%------------------------------------------------------------------------------

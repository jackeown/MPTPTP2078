%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 159 expanded)
%              Number of leaves         :   28 (  72 expanded)
%              Depth                    :    9
%              Number of atoms          :  201 ( 339 expanded)
%              Number of equality atoms :   63 ( 106 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f550,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f49,f53,f58,f62,f66,f75,f80,f84,f97,f110,f147,f199,f255,f267,f528,f546])).

fof(f546,plain,
    ( ~ spl3_8
    | spl3_14
    | ~ spl3_39 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | ~ spl3_8
    | spl3_14
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f539,f74])).

fof(f74,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_8
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f539,plain,
    ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | spl3_14
    | ~ spl3_39 ),
    inference(superposition,[],[f109,f527])).

fof(f527,plain,
    ( ! [X18] : k4_xboole_0(X18,sK2) = k4_xboole_0(k2_xboole_0(X18,k4_xboole_0(sK1,sK0)),sK2)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f526])).

fof(f526,plain,
    ( spl3_39
  <=> ! [X18] : k4_xboole_0(X18,sK2) = k4_xboole_0(k2_xboole_0(X18,k4_xboole_0(sK1,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f109,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)
    | spl3_14 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl3_14
  <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f528,plain,
    ( spl3_39
    | ~ spl3_9
    | ~ spl3_24
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f402,f265,f197,f77,f526])).

fof(f77,plain,
    ( spl3_9
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f197,plain,
    ( spl3_24
  <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f265,plain,
    ( spl3_29
  <=> ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f402,plain,
    ( ! [X18] : k4_xboole_0(X18,sK2) = k4_xboole_0(k2_xboole_0(X18,k4_xboole_0(sK1,sK0)),sK2)
    | ~ spl3_9
    | ~ spl3_24
    | ~ spl3_29 ),
    inference(forward_demodulation,[],[f362,f266])).

fof(f266,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f265])).

fof(f362,plain,
    ( ! [X18] : k4_xboole_0(k2_xboole_0(X18,k4_xboole_0(sK1,sK0)),sK2) = k2_xboole_0(k4_xboole_0(X18,sK2),k1_xboole_0)
    | ~ spl3_9
    | ~ spl3_24 ),
    inference(superposition,[],[f198,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f198,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f197])).

fof(f267,plain,
    ( spl3_29
    | ~ spl3_3
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f257,f253,f47,f265])).

fof(f47,plain,
    ( spl3_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f253,plain,
    ( spl3_28
  <=> ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f257,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl3_3
    | ~ spl3_28 ),
    inference(superposition,[],[f254,f48])).

fof(f48,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f254,plain,
    ( ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f253])).

fof(f255,plain,
    ( spl3_28
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f233,f145,f82,f51,f253])).

fof(f51,plain,
    ( spl3_4
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f82,plain,
    ( spl3_10
  <=> ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f145,plain,
    ( spl3_18
  <=> ! [X3,X4] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f233,plain,
    ( ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_18 ),
    inference(backward_demodulation,[],[f83,f216])).

fof(f216,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl3_4
    | ~ spl3_18 ),
    inference(superposition,[],[f146,f52])).

fof(f52,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f146,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f145])).

fof(f83,plain,
    ( ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) = X0
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f82])).

fof(f199,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f29,f197])).

fof(f29,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f147,plain,
    ( spl3_18
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f119,f95,f47,f145])).

fof(f95,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f119,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(superposition,[],[f96,f48])).

fof(f96,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f110,plain,
    ( ~ spl3_14
    | spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f67,f60,f55,f107])).

fof(f55,plain,
    ( spl3_5
  <=> r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f60,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f67,plain,
    ( k1_xboole_0 != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)
    | spl3_5
    | ~ spl3_6 ),
    inference(resolution,[],[f61,f57])).

fof(f57,plain,
    ( ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f60])).

fof(f97,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f28,f95])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f84,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f34,f82])).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) = X0 ),
    inference(backward_demodulation,[],[f32,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f32,plain,(
    ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(definition_unfolding,[],[f20,f30])).

fof(f30,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f20,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f80,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f69,f64,f42,f77])).

fof(f42,plain,
    ( spl3_2
  <=> r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f64,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f69,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2)
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(resolution,[],[f65,f44])).

fof(f44,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f75,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f68,f64,f37,f72])).

fof(f37,plain,
    ( spl3_1
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f68,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(resolution,[],[f65,f39])).

fof(f39,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f66,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f62,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f60])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f58,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f35,f55])).

fof(f35,plain,(
    ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) ),
    inference(backward_demodulation,[],[f31,f33])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f25,f23])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f31,plain,(
    ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK2) ),
    inference(definition_unfolding,[],[f19,f30])).

fof(f19,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
    & r1_tarski(k4_xboole_0(sK1,sK0),sK2)
    & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
        & r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
      & r1_tarski(k4_xboole_0(sK1,sK0),sK2)
      & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
          & r1_tarski(k4_xboole_0(X0,X1),X2) )
       => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
     => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).

fof(f53,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f49,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f45,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f40,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:37:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (25888)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.47  % (25898)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (25902)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (25891)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (25894)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (25890)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (25899)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (25892)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (25900)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.50  % (25897)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (25901)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (25894)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f550,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f40,f45,f49,f53,f58,f62,f66,f75,f80,f84,f97,f110,f147,f199,f255,f267,f528,f546])).
% 0.21/0.50  fof(f546,plain,(
% 0.21/0.50    ~spl3_8 | spl3_14 | ~spl3_39),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f545])).
% 0.21/0.50  fof(f545,plain,(
% 0.21/0.50    $false | (~spl3_8 | spl3_14 | ~spl3_39)),
% 0.21/0.50    inference(subsumption_resolution,[],[f539,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) | ~spl3_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl3_8 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f539,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) | (spl3_14 | ~spl3_39)),
% 0.21/0.50    inference(superposition,[],[f109,f527])).
% 0.21/0.50  fof(f527,plain,(
% 0.21/0.50    ( ! [X18] : (k4_xboole_0(X18,sK2) = k4_xboole_0(k2_xboole_0(X18,k4_xboole_0(sK1,sK0)),sK2)) ) | ~spl3_39),
% 0.21/0.50    inference(avatar_component_clause,[],[f526])).
% 0.21/0.50  fof(f526,plain,(
% 0.21/0.50    spl3_39 <=> ! [X18] : k4_xboole_0(X18,sK2) = k4_xboole_0(k2_xboole_0(X18,k4_xboole_0(sK1,sK0)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) | spl3_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f107])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    spl3_14 <=> k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.50  fof(f528,plain,(
% 0.21/0.50    spl3_39 | ~spl3_9 | ~spl3_24 | ~spl3_29),
% 0.21/0.50    inference(avatar_split_clause,[],[f402,f265,f197,f77,f526])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl3_9 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    spl3_24 <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    spl3_29 <=> ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.50  fof(f402,plain,(
% 0.21/0.50    ( ! [X18] : (k4_xboole_0(X18,sK2) = k4_xboole_0(k2_xboole_0(X18,k4_xboole_0(sK1,sK0)),sK2)) ) | (~spl3_9 | ~spl3_24 | ~spl3_29)),
% 0.21/0.50    inference(forward_demodulation,[],[f362,f266])).
% 0.21/0.50  fof(f266,plain,(
% 0.21/0.50    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) ) | ~spl3_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f265])).
% 0.21/0.50  fof(f362,plain,(
% 0.21/0.50    ( ! [X18] : (k4_xboole_0(k2_xboole_0(X18,k4_xboole_0(sK1,sK0)),sK2) = k2_xboole_0(k4_xboole_0(X18,sK2),k1_xboole_0)) ) | (~spl3_9 | ~spl3_24)),
% 0.21/0.50    inference(superposition,[],[f198,f79])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2) | ~spl3_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f77])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) ) | ~spl3_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f197])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    spl3_29 | ~spl3_3 | ~spl3_28),
% 0.21/0.50    inference(avatar_split_clause,[],[f257,f253,f47,f265])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    spl3_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    spl3_28 <=> ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.50  fof(f257,plain,(
% 0.21/0.50    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) ) | (~spl3_3 | ~spl3_28)),
% 0.21/0.50    inference(superposition,[],[f254,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f47])).
% 0.21/0.50  fof(f254,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) ) | ~spl3_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f253])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    spl3_28 | ~spl3_4 | ~spl3_10 | ~spl3_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f233,f145,f82,f51,f253])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    spl3_4 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    spl3_10 <=> ! [X0] : k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) = X0),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl3_18 <=> ! [X3,X4] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k1_xboole_0) = X0) ) | (~spl3_4 | ~spl3_10 | ~spl3_18)),
% 0.21/0.50    inference(backward_demodulation,[],[f83,f216])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | (~spl3_4 | ~spl3_18)),
% 0.21/0.50    inference(superposition,[],[f146,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) ) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f51])).
% 0.21/0.50  fof(f146,plain,(
% 0.21/0.50    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))) ) | ~spl3_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f145])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) = X0) ) | ~spl3_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f82])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    spl3_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f29,f197])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.21/0.50  fof(f147,plain,(
% 0.21/0.50    spl3_18 | ~spl3_3 | ~spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f119,f95,f47,f145])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    spl3_12 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,k1_xboole_0))) ) | (~spl3_3 | ~spl3_12)),
% 0.21/0.50    inference(superposition,[],[f96,f48])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f95])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ~spl3_14 | spl3_5 | ~spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f67,f60,f55,f107])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    spl3_5 <=> r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl3_6 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) | (spl3_5 | ~spl3_6)),
% 0.21/0.50    inference(resolution,[],[f61,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ~r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) | spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f55])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) ) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f60])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl3_12),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f95])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    spl3_10),
% 0.21/0.50    inference(avatar_split_clause,[],[f34,f82])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,X0)) = X0) )),
% 0.21/0.50    inference(backward_demodulation,[],[f32,f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(k2_xboole_0(X0,k1_xboole_0),k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) = X0) )),
% 0.21/0.50    inference(definition_unfolding,[],[f20,f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f24,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    spl3_9 | ~spl3_2 | ~spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f69,f64,f42,f77])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    spl3_2 <=> r1_tarski(k4_xboole_0(sK1,sK0),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl3_7 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2) | (~spl3_2 | ~spl3_7)),
% 0.21/0.50    inference(resolution,[],[f65,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    r1_tarski(k4_xboole_0(sK1,sK0),sK2) | ~spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f42])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f64])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    spl3_8 | ~spl3_1 | ~spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f68,f64,f37,f72])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    spl3_1 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) | (~spl3_1 | ~spl3_7)),
% 0.21/0.50    inference(resolution,[],[f65,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    r1_tarski(k4_xboole_0(sK0,sK1),sK2) | ~spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f37])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f64])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f60])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ~spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f35,f55])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ~r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)),
% 0.21/0.50    inference(backward_demodulation,[],[f31,f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f25,f23])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),sK2)),
% 0.21/0.50    inference(definition_unfolding,[],[f19,f30])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ~r1_tarski(k5_xboole_0(sK0,sK1),sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ~r1_tarski(k5_xboole_0(sK0,sK1),sK2) & r1_tarski(k4_xboole_0(sK1,sK0),sK2) & r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => (~r1_tarski(k5_xboole_0(sK0,sK1),sK2) & r1_tarski(k4_xboole_0(sK1,sK0),sK2) & r1_tarski(k4_xboole_0(sK0,sK1),sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.50    inference(flattening,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & (r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 0.21/0.50    inference(negated_conjecture,[],[f10])).
% 0.21/0.50  fof(f10,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f51])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f47])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f18,f42])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    r1_tarski(k4_xboole_0(sK1,sK0),sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f17,f37])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f15])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (25894)------------------------------
% 0.21/0.50  % (25894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (25894)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (25894)Memory used [KB]: 6524
% 0.21/0.50  % (25894)Time elapsed: 0.026 s
% 0.21/0.50  % (25894)------------------------------
% 0.21/0.50  % (25894)------------------------------
% 0.21/0.50  % (25886)Success in time 0.139 s
%------------------------------------------------------------------------------

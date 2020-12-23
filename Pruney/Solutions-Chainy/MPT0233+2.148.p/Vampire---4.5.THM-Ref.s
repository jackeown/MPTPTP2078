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
% DateTime   : Thu Dec  3 12:37:23 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 322 expanded)
%              Number of leaves         :   20 ( 106 expanded)
%              Depth                    :   10
%              Number of atoms          :  268 ( 670 expanded)
%              Number of equality atoms :  108 ( 399 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f403,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f190,f213,f218,f256,f271,f289,f320,f346,f351,f370,f402])).

fof(f402,plain,
    ( ~ spl5_4
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f394])).

fof(f394,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f353,f72,f387])).

fof(f387,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X3 )
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(duplicate_literal_removal,[],[f380])).

fof(f380,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X3
        | sK1 = X3 )
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(superposition,[],[f73,f371])).

fof(f371,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl5_4
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f189,f319])).

fof(f319,plain,
    ( sK1 = sK2
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f317])).

fof(f317,plain,
    ( spl5_10
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f189,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f187])).

fof(f187,plain,
    ( spl5_4
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f31,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f72,plain,(
    ! [X3,X1] : r2_hidden(X3,k5_enumset1(X3,X3,X3,X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k5_enumset1(X3,X3,X3,X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f38,f51])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f353,plain,
    ( sK0 != sK1
    | ~ spl5_10 ),
    inference(superposition,[],[f23,f319])).

fof(f23,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f370,plain,
    ( ~ spl5_2
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_contradiction_clause,[],[f361])).

fof(f361,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f260,f72,f360])).

fof(f360,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X3 )
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(duplicate_literal_removal,[],[f359])).

fof(f359,plain,
    ( ! [X3] :
        ( sK1 = X3
        | ~ r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X3 )
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f333,f319])).

fof(f333,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X3
        | sK2 = X3 )
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(superposition,[],[f73,f321])).

fof(f321,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1)
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f181,f212])).

fof(f212,plain,
    ( sK1 = sK3
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl5_6
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f181,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f179])).

fof(f179,plain,
    ( spl5_2
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f260,plain,
    ( sK0 != sK1
    | ~ spl5_6 ),
    inference(superposition,[],[f24,f212])).

fof(f24,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f16])).

fof(f351,plain,(
    ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f347])).

fof(f347,plain,
    ( $false
    | ~ spl5_9 ),
    inference(subsumption_resolution,[],[f23,f315])).

fof(f315,plain,
    ( sK0 = sK2
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl5_9
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f346,plain,
    ( spl5_9
    | spl5_10
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f344,f210,f179,f317,f313])).

fof(f344,plain,
    ( sK1 = sK2
    | sK0 = sK2
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(resolution,[],[f332,f73])).

fof(f332,plain,
    ( r2_hidden(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_2
    | ~ spl5_6 ),
    inference(superposition,[],[f72,f321])).

fof(f320,plain,
    ( spl5_9
    | spl5_10
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f310,f187,f317,f313])).

fof(f310,plain,
    ( sK1 = sK2
    | sK0 = sK2
    | ~ spl5_4 ),
    inference(resolution,[],[f296,f73])).

fof(f296,plain,
    ( r2_hidden(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_4 ),
    inference(superposition,[],[f70,f189])).

fof(f70,plain,(
    ! [X0,X3] : r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X3)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f39,f51])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f289,plain,(
    ~ spl5_1 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f97,f279])).

fof(f279,plain,
    ( r2_hidden(sK1,k1_xboole_0)
    | ~ spl5_1 ),
    inference(superposition,[],[f70,f177])).

fof(f177,plain,
    ( k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl5_1
  <=> k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f97,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f95,f81])).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f79,f80])).

fof(f80,plain,(
    ! [X0] : r1_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0) ),
    inference(superposition,[],[f55,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0)) ),
    inference(definition_unfolding,[],[f25,f32])).

fof(f32,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f55,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f30,f32])).

fof(f30,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X0)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f49,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,X0)) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,k1_xboole_0)
      | ~ r2_hidden(X1,k3_xboole_0(k1_xboole_0,X0)) ) ),
    inference(superposition,[],[f41,f53])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f271,plain,
    ( ~ spl5_3
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f263])).

fof(f263,plain,
    ( $false
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(unit_resulting_resolution,[],[f260,f72,f262])).

fof(f262,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK1 = X3 )
    | ~ spl5_3
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f234,f212])).

fof(f234,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK3 = X3 )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
        | sK3 = X3
        | sK3 = X3 )
    | ~ spl5_3 ),
    inference(superposition,[],[f73,f185])).

fof(f185,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f183])).

fof(f183,plain,
    ( spl5_3
  <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f256,plain,
    ( spl5_5
    | spl5_6
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f254,f183,f210,f206])).

fof(f206,plain,
    ( spl5_5
  <=> sK0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f254,plain,
    ( sK1 = sK3
    | sK0 = sK3
    | ~ spl5_3 ),
    inference(resolution,[],[f225,f73])).

fof(f225,plain,
    ( r2_hidden(sK3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_3 ),
    inference(superposition,[],[f70,f185])).

fof(f218,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f214])).

fof(f214,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f24,f208])).

fof(f208,plain,
    ( sK0 = sK3
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f206])).

fof(f213,plain,
    ( spl5_5
    | spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f203,f179,f210,f206])).

fof(f203,plain,
    ( sK1 = sK3
    | sK0 = sK3
    | ~ spl5_2 ),
    inference(resolution,[],[f197,f73])).

fof(f197,plain,
    ( r2_hidden(sK3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl5_2 ),
    inference(superposition,[],[f70,f181])).

fof(f190,plain,
    ( spl5_1
    | spl5_2
    | spl5_3
    | spl5_4 ),
    inference(avatar_split_clause,[],[f169,f187,f183,f179,f175])).

fof(f169,plain,
    ( k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)
    | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)
    | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(resolution,[],[f66,f52])).

fof(f52,plain,(
    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    inference(definition_unfolding,[],[f22,f51,f51])).

fof(f22,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2))
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0
      | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) = X0
      | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f44,f26,f26,f51,f51])).

fof(f26,plain,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n013.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 20:41:54 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.19/0.47  % (8286)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.48  % (8286)Refutation not found, incomplete strategy% (8286)------------------------------
% 0.19/0.48  % (8286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (8286)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (8286)Memory used [KB]: 1663
% 0.19/0.48  % (8286)Time elapsed: 0.088 s
% 0.19/0.48  % (8286)------------------------------
% 0.19/0.48  % (8286)------------------------------
% 0.19/0.49  % (8288)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.49  % (8290)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.49  % (8294)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.50  % (8304)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.19/0.50  % (8292)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.50  % (8287)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.50  % (8296)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.51  % (8298)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.19/0.51  % (8297)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.19/0.51  % (8311)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.51  % (8289)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (8314)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.19/0.51  % (8314)Refutation not found, incomplete strategy% (8314)------------------------------
% 0.19/0.51  % (8314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (8314)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (8314)Memory used [KB]: 1663
% 0.19/0.51  % (8314)Time elapsed: 0.100 s
% 0.19/0.51  % (8314)------------------------------
% 0.19/0.51  % (8314)------------------------------
% 0.19/0.51  % (8311)Refutation not found, incomplete strategy% (8311)------------------------------
% 0.19/0.51  % (8311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (8311)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (8311)Memory used [KB]: 6268
% 0.19/0.51  % (8311)Time elapsed: 0.134 s
% 0.19/0.51  % (8311)------------------------------
% 0.19/0.51  % (8311)------------------------------
% 0.19/0.52  % (8300)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.52  % (8303)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.19/0.52  % (8285)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.52  % (8307)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.52  % (8313)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.52  % (8312)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.19/0.52  % (8312)Refutation not found, incomplete strategy% (8312)------------------------------
% 0.19/0.52  % (8312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (8312)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (8312)Memory used [KB]: 6268
% 0.19/0.52  % (8312)Time elapsed: 0.131 s
% 0.19/0.52  % (8312)------------------------------
% 0.19/0.52  % (8312)------------------------------
% 0.19/0.52  % (8305)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.19/0.52  % (8308)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.52  % (8306)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.53  % (8297)Refutation not found, incomplete strategy% (8297)------------------------------
% 0.19/0.53  % (8297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (8297)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (8297)Memory used [KB]: 10618
% 0.19/0.53  % (8297)Time elapsed: 0.142 s
% 0.19/0.53  % (8297)------------------------------
% 0.19/0.53  % (8297)------------------------------
% 0.19/0.53  % (8299)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.54  % (8291)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.54  % (8293)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.55  % (8309)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.59/0.55  % (8310)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.59/0.55  % (8301)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.59/0.55  % (8295)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.59/0.55  % (8302)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.59/0.55  % (8301)Refutation not found, incomplete strategy% (8301)------------------------------
% 1.59/0.55  % (8301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.55  % (8301)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.55  
% 1.59/0.55  % (8301)Memory used [KB]: 10618
% 1.59/0.55  % (8301)Time elapsed: 0.153 s
% 1.59/0.55  % (8301)------------------------------
% 1.59/0.55  % (8301)------------------------------
% 1.59/0.56  % (8298)Refutation found. Thanks to Tanya!
% 1.59/0.56  % SZS status Theorem for theBenchmark
% 1.59/0.56  % SZS output start Proof for theBenchmark
% 1.59/0.56  fof(f403,plain,(
% 1.59/0.56    $false),
% 1.59/0.56    inference(avatar_sat_refutation,[],[f190,f213,f218,f256,f271,f289,f320,f346,f351,f370,f402])).
% 1.59/0.56  fof(f402,plain,(
% 1.59/0.56    ~spl5_4 | ~spl5_10),
% 1.59/0.56    inference(avatar_contradiction_clause,[],[f394])).
% 1.59/0.56  fof(f394,plain,(
% 1.59/0.56    $false | (~spl5_4 | ~spl5_10)),
% 1.59/0.56    inference(unit_resulting_resolution,[],[f353,f72,f387])).
% 1.59/0.56  fof(f387,plain,(
% 1.59/0.56    ( ! [X3] : (~r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X3) ) | (~spl5_4 | ~spl5_10)),
% 1.59/0.56    inference(duplicate_literal_removal,[],[f380])).
% 1.59/0.56  fof(f380,plain,(
% 1.59/0.56    ( ! [X3] : (~r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X3 | sK1 = X3) ) | (~spl5_4 | ~spl5_10)),
% 1.59/0.56    inference(superposition,[],[f73,f371])).
% 1.59/0.56  fof(f371,plain,(
% 1.59/0.56    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1) | (~spl5_4 | ~spl5_10)),
% 1.59/0.56    inference(forward_demodulation,[],[f189,f319])).
% 1.59/0.56  fof(f319,plain,(
% 1.59/0.56    sK1 = sK2 | ~spl5_10),
% 1.59/0.56    inference(avatar_component_clause,[],[f317])).
% 1.59/0.56  fof(f317,plain,(
% 1.59/0.56    spl5_10 <=> sK1 = sK2),
% 1.59/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.59/0.56  fof(f189,plain,(
% 1.59/0.56    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl5_4),
% 1.59/0.56    inference(avatar_component_clause,[],[f187])).
% 1.59/0.56  fof(f187,plain,(
% 1.59/0.56    spl5_4 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 1.59/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.59/0.56  fof(f73,plain,(
% 1.59/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 1.59/0.56    inference(equality_resolution,[],[f58])).
% 1.59/0.56  fof(f58,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 1.59/0.56    inference(definition_unfolding,[],[f37,f51])).
% 1.59/0.56  fof(f51,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 1.59/0.56    inference(definition_unfolding,[],[f31,f33])).
% 1.59/0.56  fof(f33,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f9])).
% 1.59/0.56  fof(f9,axiom,(
% 1.59/0.56    ! [X0,X1,X2] : k5_enumset1(X0,X0,X0,X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_enumset1)).
% 1.59/0.56  fof(f31,plain,(
% 1.59/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f8])).
% 1.59/0.56  fof(f8,axiom,(
% 1.59/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.59/0.56  fof(f37,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.59/0.56    inference(cnf_transformation,[],[f7])).
% 1.59/0.56  fof(f7,axiom,(
% 1.59/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.74/0.56  fof(f72,plain,(
% 1.74/0.56    ( ! [X3,X1] : (r2_hidden(X3,k5_enumset1(X3,X3,X3,X3,X3,X3,X1))) )),
% 1.74/0.56    inference(equality_resolution,[],[f71])).
% 1.74/0.56  fof(f71,plain,(
% 1.74/0.56    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k5_enumset1(X3,X3,X3,X3,X3,X3,X1) != X2) )),
% 1.74/0.56    inference(equality_resolution,[],[f57])).
% 1.74/0.56  fof(f57,plain,(
% 1.74/0.56    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 1.74/0.56    inference(definition_unfolding,[],[f38,f51])).
% 1.74/0.56  fof(f38,plain,(
% 1.74/0.56    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.74/0.56    inference(cnf_transformation,[],[f7])).
% 1.74/0.56  fof(f353,plain,(
% 1.74/0.56    sK0 != sK1 | ~spl5_10),
% 1.74/0.56    inference(superposition,[],[f23,f319])).
% 1.74/0.56  fof(f23,plain,(
% 1.74/0.56    sK0 != sK2),
% 1.74/0.56    inference(cnf_transformation,[],[f16])).
% 1.74/0.56  fof(f16,plain,(
% 1.74/0.56    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.74/0.56    inference(ennf_transformation,[],[f15])).
% 1.74/0.56  fof(f15,negated_conjecture,(
% 1.74/0.56    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.74/0.56    inference(negated_conjecture,[],[f14])).
% 1.74/0.56  fof(f14,conjecture,(
% 1.74/0.56    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 1.74/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 1.74/0.56  fof(f370,plain,(
% 1.74/0.56    ~spl5_2 | ~spl5_6 | ~spl5_10),
% 1.74/0.56    inference(avatar_contradiction_clause,[],[f361])).
% 1.74/0.56  fof(f361,plain,(
% 1.74/0.56    $false | (~spl5_2 | ~spl5_6 | ~spl5_10)),
% 1.74/0.56    inference(unit_resulting_resolution,[],[f260,f72,f360])).
% 1.74/0.56  fof(f360,plain,(
% 1.74/0.56    ( ! [X3] : (~r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X3) ) | (~spl5_2 | ~spl5_6 | ~spl5_10)),
% 1.74/0.56    inference(duplicate_literal_removal,[],[f359])).
% 1.74/0.56  fof(f359,plain,(
% 1.74/0.56    ( ! [X3] : (sK1 = X3 | ~r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X3) ) | (~spl5_2 | ~spl5_6 | ~spl5_10)),
% 1.74/0.56    inference(forward_demodulation,[],[f333,f319])).
% 1.74/0.56  fof(f333,plain,(
% 1.74/0.56    ( ! [X3] : (~r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X3 | sK2 = X3) ) | (~spl5_2 | ~spl5_6)),
% 1.74/0.56    inference(superposition,[],[f73,f321])).
% 1.74/0.56  fof(f321,plain,(
% 1.74/0.56    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK1) | (~spl5_2 | ~spl5_6)),
% 1.74/0.56    inference(forward_demodulation,[],[f181,f212])).
% 1.74/0.56  fof(f212,plain,(
% 1.74/0.56    sK1 = sK3 | ~spl5_6),
% 1.74/0.56    inference(avatar_component_clause,[],[f210])).
% 1.74/0.56  fof(f210,plain,(
% 1.74/0.56    spl5_6 <=> sK1 = sK3),
% 1.74/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.74/0.56  fof(f181,plain,(
% 1.74/0.56    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) | ~spl5_2),
% 1.74/0.56    inference(avatar_component_clause,[],[f179])).
% 1.74/0.56  fof(f179,plain,(
% 1.74/0.56    spl5_2 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)),
% 1.74/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.74/0.56  fof(f260,plain,(
% 1.74/0.56    sK0 != sK1 | ~spl5_6),
% 1.74/0.56    inference(superposition,[],[f24,f212])).
% 1.74/0.56  fof(f24,plain,(
% 1.74/0.56    sK0 != sK3),
% 1.74/0.56    inference(cnf_transformation,[],[f16])).
% 1.74/0.56  fof(f351,plain,(
% 1.74/0.56    ~spl5_9),
% 1.74/0.56    inference(avatar_contradiction_clause,[],[f347])).
% 1.74/0.56  fof(f347,plain,(
% 1.74/0.56    $false | ~spl5_9),
% 1.74/0.56    inference(subsumption_resolution,[],[f23,f315])).
% 1.74/0.56  fof(f315,plain,(
% 1.74/0.56    sK0 = sK2 | ~spl5_9),
% 1.74/0.56    inference(avatar_component_clause,[],[f313])).
% 1.74/0.56  fof(f313,plain,(
% 1.74/0.56    spl5_9 <=> sK0 = sK2),
% 1.74/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.74/0.56  fof(f346,plain,(
% 1.74/0.56    spl5_9 | spl5_10 | ~spl5_2 | ~spl5_6),
% 1.74/0.56    inference(avatar_split_clause,[],[f344,f210,f179,f317,f313])).
% 1.74/0.56  fof(f344,plain,(
% 1.74/0.56    sK1 = sK2 | sK0 = sK2 | (~spl5_2 | ~spl5_6)),
% 1.74/0.56    inference(resolution,[],[f332,f73])).
% 1.74/0.56  fof(f332,plain,(
% 1.74/0.56    r2_hidden(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | (~spl5_2 | ~spl5_6)),
% 1.74/0.56    inference(superposition,[],[f72,f321])).
% 1.74/0.56  fof(f320,plain,(
% 1.74/0.56    spl5_9 | spl5_10 | ~spl5_4),
% 1.74/0.56    inference(avatar_split_clause,[],[f310,f187,f317,f313])).
% 1.74/0.56  fof(f310,plain,(
% 1.74/0.56    sK1 = sK2 | sK0 = sK2 | ~spl5_4),
% 1.74/0.56    inference(resolution,[],[f296,f73])).
% 1.74/0.56  fof(f296,plain,(
% 1.74/0.56    r2_hidden(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_4),
% 1.74/0.56    inference(superposition,[],[f70,f189])).
% 1.74/0.56  fof(f70,plain,(
% 1.74/0.56    ( ! [X0,X3] : (r2_hidden(X3,k5_enumset1(X0,X0,X0,X0,X0,X0,X3))) )),
% 1.74/0.56    inference(equality_resolution,[],[f69])).
% 1.74/0.56  fof(f69,plain,(
% 1.74/0.56    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k5_enumset1(X0,X0,X0,X0,X0,X0,X3) != X2) )),
% 1.74/0.56    inference(equality_resolution,[],[f56])).
% 1.74/0.56  fof(f56,plain,(
% 1.74/0.56    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k5_enumset1(X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 1.74/0.56    inference(definition_unfolding,[],[f39,f51])).
% 1.74/0.56  fof(f39,plain,(
% 1.74/0.56    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.74/0.56    inference(cnf_transformation,[],[f7])).
% 1.74/0.56  fof(f289,plain,(
% 1.74/0.56    ~spl5_1),
% 1.74/0.56    inference(avatar_contradiction_clause,[],[f286])).
% 1.74/0.56  fof(f286,plain,(
% 1.74/0.56    $false | ~spl5_1),
% 1.74/0.56    inference(unit_resulting_resolution,[],[f97,f279])).
% 1.74/0.56  fof(f279,plain,(
% 1.74/0.56    r2_hidden(sK1,k1_xboole_0) | ~spl5_1),
% 1.74/0.56    inference(superposition,[],[f70,f177])).
% 1.74/0.56  fof(f177,plain,(
% 1.74/0.56    k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) | ~spl5_1),
% 1.74/0.56    inference(avatar_component_clause,[],[f175])).
% 1.74/0.56  fof(f175,plain,(
% 1.74/0.56    spl5_1 <=> k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 1.74/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.74/0.56  fof(f97,plain,(
% 1.74/0.56    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 1.74/0.56    inference(duplicate_literal_removal,[],[f96])).
% 1.74/0.56  fof(f96,plain,(
% 1.74/0.56    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0)) )),
% 1.74/0.56    inference(forward_demodulation,[],[f95,f81])).
% 1.74/0.56  fof(f81,plain,(
% 1.74/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 1.74/0.56    inference(resolution,[],[f79,f80])).
% 1.74/0.56  fof(f80,plain,(
% 1.74/0.56    ( ! [X0] : (r1_xboole_0(k3_xboole_0(k1_xboole_0,X0),k1_xboole_0)) )),
% 1.74/0.56    inference(superposition,[],[f55,f53])).
% 1.74/0.56  fof(f53,plain,(
% 1.74/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.74/0.56    inference(definition_unfolding,[],[f25,f32])).
% 1.74/0.56  fof(f32,plain,(
% 1.74/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.74/0.56    inference(cnf_transformation,[],[f2])).
% 1.74/0.56  fof(f2,axiom,(
% 1.74/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.74/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.74/0.56  fof(f25,plain,(
% 1.74/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.74/0.56    inference(cnf_transformation,[],[f3])).
% 1.74/0.56  fof(f3,axiom,(
% 1.74/0.56    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.74/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.74/0.56  fof(f55,plain,(
% 1.74/0.56    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,k3_xboole_0(X0,X1)))) )),
% 1.74/0.56    inference(definition_unfolding,[],[f30,f32])).
% 1.74/0.56  fof(f30,plain,(
% 1.74/0.56    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 1.74/0.56    inference(cnf_transformation,[],[f6])).
% 1.74/0.56  fof(f6,axiom,(
% 1.74/0.56    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 1.74/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).
% 1.74/0.56  fof(f79,plain,(
% 1.74/0.56    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X0) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.74/0.56    inference(resolution,[],[f49,f27])).
% 1.74/0.56  fof(f27,plain,(
% 1.74/0.56    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.74/0.56    inference(cnf_transformation,[],[f17])).
% 1.74/0.56  fof(f17,plain,(
% 1.74/0.56    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.74/0.56    inference(ennf_transformation,[],[f4])).
% 1.74/0.56  fof(f4,axiom,(
% 1.74/0.56    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.74/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.74/0.56  fof(f49,plain,(
% 1.74/0.56    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 1.74/0.56    inference(cnf_transformation,[],[f20])).
% 1.74/0.56  fof(f20,plain,(
% 1.74/0.56    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.74/0.56    inference(ennf_transformation,[],[f5])).
% 1.74/0.56  fof(f5,axiom,(
% 1.74/0.56    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.74/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_xboole_1)).
% 1.74/0.56  fof(f95,plain,(
% 1.74/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.74/0.56    inference(duplicate_literal_removal,[],[f92])).
% 1.74/0.56  fof(f92,plain,(
% 1.74/0.56    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k1_xboole_0) | ~r2_hidden(X1,k3_xboole_0(k1_xboole_0,X0))) )),
% 1.74/0.56    inference(superposition,[],[f41,f53])).
% 1.74/0.56  fof(f41,plain,(
% 1.74/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.74/0.56    inference(cnf_transformation,[],[f18])).
% 1.74/0.56  fof(f18,plain,(
% 1.74/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 1.74/0.56    inference(ennf_transformation,[],[f1])).
% 1.74/0.56  fof(f1,axiom,(
% 1.74/0.56    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 1.74/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 1.74/0.56  fof(f271,plain,(
% 1.74/0.56    ~spl5_3 | ~spl5_6),
% 1.74/0.56    inference(avatar_contradiction_clause,[],[f263])).
% 1.74/0.56  fof(f263,plain,(
% 1.74/0.56    $false | (~spl5_3 | ~spl5_6)),
% 1.74/0.56    inference(unit_resulting_resolution,[],[f260,f72,f262])).
% 1.74/0.56  fof(f262,plain,(
% 1.74/0.56    ( ! [X3] : (~r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK1 = X3) ) | (~spl5_3 | ~spl5_6)),
% 1.74/0.56    inference(forward_demodulation,[],[f234,f212])).
% 1.74/0.56  fof(f234,plain,(
% 1.74/0.56    ( ! [X3] : (~r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK3 = X3) ) | ~spl5_3),
% 1.74/0.56    inference(duplicate_literal_removal,[],[f227])).
% 1.74/0.56  fof(f227,plain,(
% 1.74/0.56    ( ! [X3] : (~r2_hidden(X3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | sK3 = X3 | sK3 = X3) ) | ~spl5_3),
% 1.74/0.56    inference(superposition,[],[f73,f185])).
% 1.74/0.56  fof(f185,plain,(
% 1.74/0.56    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) | ~spl5_3),
% 1.74/0.56    inference(avatar_component_clause,[],[f183])).
% 1.74/0.56  fof(f183,plain,(
% 1.74/0.56    spl5_3 <=> k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3)),
% 1.74/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.74/0.56  fof(f256,plain,(
% 1.74/0.56    spl5_5 | spl5_6 | ~spl5_3),
% 1.74/0.56    inference(avatar_split_clause,[],[f254,f183,f210,f206])).
% 1.74/0.56  fof(f206,plain,(
% 1.74/0.56    spl5_5 <=> sK0 = sK3),
% 1.74/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.74/0.56  fof(f254,plain,(
% 1.74/0.56    sK1 = sK3 | sK0 = sK3 | ~spl5_3),
% 1.74/0.56    inference(resolution,[],[f225,f73])).
% 1.74/0.56  fof(f225,plain,(
% 1.74/0.56    r2_hidden(sK3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_3),
% 1.74/0.56    inference(superposition,[],[f70,f185])).
% 1.74/0.56  fof(f218,plain,(
% 1.74/0.56    ~spl5_5),
% 1.74/0.56    inference(avatar_contradiction_clause,[],[f214])).
% 1.74/0.56  fof(f214,plain,(
% 1.74/0.56    $false | ~spl5_5),
% 1.74/0.56    inference(subsumption_resolution,[],[f24,f208])).
% 1.74/0.56  fof(f208,plain,(
% 1.74/0.56    sK0 = sK3 | ~spl5_5),
% 1.74/0.56    inference(avatar_component_clause,[],[f206])).
% 1.74/0.56  fof(f213,plain,(
% 1.74/0.56    spl5_5 | spl5_6 | ~spl5_2),
% 1.74/0.56    inference(avatar_split_clause,[],[f203,f179,f210,f206])).
% 1.74/0.56  fof(f203,plain,(
% 1.74/0.56    sK1 = sK3 | sK0 = sK3 | ~spl5_2),
% 1.74/0.56    inference(resolution,[],[f197,f73])).
% 1.74/0.56  fof(f197,plain,(
% 1.74/0.56    r2_hidden(sK3,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl5_2),
% 1.74/0.56    inference(superposition,[],[f70,f181])).
% 1.74/0.56  fof(f190,plain,(
% 1.74/0.56    spl5_1 | spl5_2 | spl5_3 | spl5_4),
% 1.74/0.56    inference(avatar_split_clause,[],[f169,f187,f183,f179,f175])).
% 1.74/0.56  fof(f169,plain,(
% 1.74/0.56    k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3) | k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3) | k1_xboole_0 = k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 1.74/0.56    inference(resolution,[],[f66,f52])).
% 1.74/0.56  fof(f52,plain,(
% 1.74/0.56    r1_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 1.74/0.56    inference(definition_unfolding,[],[f22,f51,f51])).
% 1.74/0.56  fof(f22,plain,(
% 1.74/0.56    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 1.74/0.56    inference(cnf_transformation,[],[f16])).
% 1.74/0.56  fof(f66,plain,(
% 1.74/0.56    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_enumset1(X1,X1,X1,X1,X1,X1,X2)) | k5_enumset1(X1,X1,X1,X1,X1,X1,X1) = X0 | k5_enumset1(X2,X2,X2,X2,X2,X2,X2) = X0 | k5_enumset1(X1,X1,X1,X1,X1,X1,X2) = X0 | k1_xboole_0 = X0) )),
% 1.74/0.56    inference(definition_unfolding,[],[f44,f26,f26,f51,f51])).
% 1.74/0.56  fof(f26,plain,(
% 1.74/0.56    ( ! [X0] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)) )),
% 1.74/0.56    inference(cnf_transformation,[],[f10])).
% 1.74/0.56  fof(f10,axiom,(
% 1.74/0.56    ! [X0] : k5_enumset1(X0,X0,X0,X0,X0,X0,X0) = k1_tarski(X0)),
% 1.74/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_enumset1)).
% 1.74/0.56  fof(f44,plain,(
% 1.74/0.56    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.74/0.56    inference(cnf_transformation,[],[f19])).
% 1.74/0.56  fof(f19,plain,(
% 1.74/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.74/0.56    inference(ennf_transformation,[],[f11])).
% 1.74/0.56  fof(f11,axiom,(
% 1.74/0.56    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.74/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.74/0.56  % SZS output end Proof for theBenchmark
% 1.74/0.56  % (8298)------------------------------
% 1.74/0.56  % (8298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.56  % (8298)Termination reason: Refutation
% 1.74/0.56  
% 1.74/0.56  % (8298)Memory used [KB]: 6396
% 1.74/0.56  % (8298)Time elapsed: 0.165 s
% 1.74/0.56  % (8298)------------------------------
% 1.74/0.56  % (8298)------------------------------
% 1.74/0.57  % (8284)Success in time 0.219 s
%------------------------------------------------------------------------------

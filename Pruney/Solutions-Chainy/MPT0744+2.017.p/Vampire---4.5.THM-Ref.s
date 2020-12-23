%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  117 ( 204 expanded)
%              Number of leaves         :   27 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  493 ( 839 expanded)
%              Number of equality atoms :  138 ( 166 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f104,f113,f114,f180,f186,f195,f204,f212,f221,f253,f264,f275,f284,f285])).

fof(f285,plain,
    ( sK0 != sK1
    | r2_hidden(sK0,sK1)
    | ~ r2_hidden(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f284,plain,
    ( ~ spl4_3
    | spl4_8
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl4_3
    | spl4_8
    | spl4_10 ),
    inference(unit_resulting_resolution,[],[f194,f107,f202,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f63,f74])).

fof(f74,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f67,f73])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f72,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f72,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f67,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f202,plain,
    ( sK0 != sK1
    | spl4_10 ),
    inference(avatar_component_clause,[],[f201])).

fof(f201,plain,
    ( spl4_10
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f107,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_3
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f194,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl4_8
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f275,plain,
    ( ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f179,f193,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f193,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f192])).

fof(f179,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl4_6
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f264,plain,(
    spl4_14 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl4_14 ),
    inference(unit_resulting_resolution,[],[f81,f252])).

fof(f252,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f250])).

fof(f250,plain,
    ( spl4_14
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f81,plain,(
    ! [X6,X2,X0,X1] : r2_hidden(X6,k2_enumset1(X0,X1,X2,X6)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X1] :
      ( r2_hidden(X6,X4)
      | k2_enumset1(X0,X1,X2,X6) != X4 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X3,X1] :
      ( r2_hidden(X6,X4)
      | X3 != X6
      | k2_enumset1(X0,X1,X2,X3) != X4 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ( ( ( sK2(X0,X1,X2,X3,X4) != X3
              & sK2(X0,X1,X2,X3,X4) != X2
              & sK2(X0,X1,X2,X3,X4) != X1
              & sK2(X0,X1,X2,X3,X4) != X0 )
            | ~ r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
          & ( sK2(X0,X1,X2,X3,X4) = X3
            | sK2(X0,X1,X2,X3,X4) = X2
            | sK2(X0,X1,X2,X3,X4) = X1
            | sK2(X0,X1,X2,X3,X4) = X0
            | r2_hidden(sK2(X0,X1,X2,X3,X4),X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).

fof(f29,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X5] :
          ( ( ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 )
            | ~ r2_hidden(X5,X4) )
          & ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5
            | r2_hidden(X5,X4) ) )
     => ( ( ( sK2(X0,X1,X2,X3,X4) != X3
            & sK2(X0,X1,X2,X3,X4) != X2
            & sK2(X0,X1,X2,X3,X4) != X1
            & sK2(X0,X1,X2,X3,X4) != X0 )
          | ~ r2_hidden(sK2(X0,X1,X2,X3,X4),X4) )
        & ( sK2(X0,X1,X2,X3,X4) = X3
          | sK2(X0,X1,X2,X3,X4) = X2
          | sK2(X0,X1,X2,X3,X4) = X1
          | sK2(X0,X1,X2,X3,X4) = X0
          | r2_hidden(sK2(X0,X1,X2,X3,X4),X4) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X4)
              | ( X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(rectify,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_enumset1(X0,X1,X2,X3) = X4
        | ? [X5] :
            ( ( ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 )
              | ~ r2_hidden(X5,X4) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | r2_hidden(X5,X4) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X4)
              | ( X3 != X5
                & X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X3 = X5
              | X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X4) ) )
        | k2_enumset1(X0,X1,X2,X3) != X4 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ( X3 = X5
            | X2 = X5
            | X1 = X5
            | X0 = X5 ) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( k2_enumset1(X0,X1,X2,X3) = X4
    <=> ! [X5] :
          ( r2_hidden(X5,X4)
        <=> ~ ( X3 != X5
              & X2 != X5
              & X1 != X5
              & X0 != X5 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).

fof(f253,plain,
    ( ~ spl4_14
    | ~ spl4_10
    | spl4_11 ),
    inference(avatar_split_clause,[],[f231,f209,f201,f250])).

fof(f209,plain,
    ( spl4_11
  <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f231,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_10
    | spl4_11 ),
    inference(superposition,[],[f211,f203])).

fof(f203,plain,
    ( sK0 = sK1
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f201])).

fof(f211,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl4_11 ),
    inference(avatar_component_clause,[],[f209])).

fof(f221,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_8
    | spl4_9 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_8
    | spl4_9 ),
    inference(unit_resulting_resolution,[],[f98,f103,f194,f199,f175])).

fof(f175,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f46,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f199,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f197])).

fof(f197,plain,
    ( spl4_9
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f103,plain,
    ( v3_ordinal1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_2
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f98,plain,
    ( v3_ordinal1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f212,plain,
    ( ~ spl4_11
    | spl4_3 ),
    inference(avatar_split_clause,[],[f190,f106,f209])).

fof(f190,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl4_3 ),
    inference(resolution,[],[f108,f89])).

fof(f89,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & ~ r2_hidden(sK3(X0,X1,X2),X0) )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( r2_hidden(sK3(X0,X1,X2),X1)
            | r2_hidden(sK3(X0,X1,X2),X0)
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & ~ r2_hidden(sK3(X0,X1,X2),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( r2_hidden(sK3(X0,X1,X2),X1)
          | r2_hidden(sK3(X0,X1,X2),X0)
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( ~ r2_hidden(X3,X1)
                & ~ r2_hidden(X3,X0) ) )
            & ( r2_hidden(X3,X1)
              | r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f108,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f204,plain,
    ( ~ spl4_9
    | spl4_10
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f188,f183,f201,f197])).

fof(f183,plain,
    ( spl4_7
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f188,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f185,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f185,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f183])).

fof(f195,plain,
    ( ~ spl4_8
    | spl4_3 ),
    inference(avatar_split_clause,[],[f189,f106,f192])).

fof(f189,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_3 ),
    inference(resolution,[],[f108,f90])).

fof(f90,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f186,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f181,f110,f183,f101,f96])).

fof(f110,plain,
    ( spl4_4
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f181,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f111,f44])).

fof(f111,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f180,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_6
    | spl4_4 ),
    inference(avatar_split_clause,[],[f173,f110,f177,f101,f96])).

fof(f173,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl4_4 ),
    inference(resolution,[],[f46,f112])).

fof(f112,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f114,plain,
    ( spl4_3
    | spl4_4 ),
    inference(avatar_split_clause,[],[f76,f110,f106])).

fof(f76,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f42,f74])).

fof(f42,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) )
            & ( r1_ordinal1(X0,X1)
              | r2_hidden(X0,k1_ordinal1(X1)) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(sK0,X1)
            | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(sK0,X1)
            | r2_hidden(sK0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(sK0,X1)
          | ~ r2_hidden(sK0,k1_ordinal1(X1)) )
        & ( r1_ordinal1(sK0,X1)
          | r2_hidden(sK0,k1_ordinal1(X1)) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(sK0,sK1)
        | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
      & ( r1_ordinal1(sK0,sK1)
        | r2_hidden(sK0,k1_ordinal1(sK1)) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f113,plain,
    ( ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f75,f110,f106])).

fof(f75,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f43,f74])).

fof(f43,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f104,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f41,f101])).

fof(f41,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f99,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f40,f96])).

fof(f40,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:26:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (6778)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.46  % (6786)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.46  % (6770)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.48  % (6786)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f286,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f99,f104,f113,f114,f180,f186,f195,f204,f212,f221,f253,f264,f275,f284,f285])).
% 0.20/0.48  fof(f285,plain,(
% 0.20/0.48    sK0 != sK1 | r2_hidden(sK0,sK1) | ~r2_hidden(sK1,sK0)),
% 0.20/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.48  fof(f284,plain,(
% 0.20/0.48    ~spl4_3 | spl4_8 | spl4_10),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f283])).
% 0.20/0.48  fof(f283,plain,(
% 0.20/0.48    $false | (~spl4_3 | spl4_8 | spl4_10)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f194,f107,f202,f79])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k2_enumset1(X1,X1,X1,X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 0.20/0.48    inference(definition_unfolding,[],[f63,f74])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_enumset1(X0,X0,X0,X0))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f67,f73])).
% 0.20/0.48  fof(f73,plain,(
% 0.20/0.48    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f72,f71])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.48    inference(flattening,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.20/0.48    inference(nnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.20/0.48  fof(f202,plain,(
% 0.20/0.48    sK0 != sK1 | spl4_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f201])).
% 0.20/0.48  fof(f201,plain,(
% 0.20/0.48    spl4_10 <=> sK0 = sK1),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) | ~spl4_3),
% 0.20/0.48    inference(avatar_component_clause,[],[f106])).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl4_3 <=> r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.48  fof(f194,plain,(
% 0.20/0.48    ~r2_hidden(sK0,sK1) | spl4_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f192])).
% 0.20/0.48  fof(f192,plain,(
% 0.20/0.48    spl4_8 <=> r2_hidden(sK0,sK1)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.48  fof(f275,plain,(
% 0.20/0.48    ~spl4_6 | ~spl4_8),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f272])).
% 0.20/0.48  fof(f272,plain,(
% 0.20/0.48    $false | (~spl4_6 | ~spl4_8)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f179,f193,f66])).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    r2_hidden(sK0,sK1) | ~spl4_8),
% 0.20/0.48    inference(avatar_component_clause,[],[f192])).
% 0.20/0.48  fof(f179,plain,(
% 0.20/0.48    r2_hidden(sK1,sK0) | ~spl4_6),
% 0.20/0.48    inference(avatar_component_clause,[],[f177])).
% 0.20/0.48  fof(f177,plain,(
% 0.20/0.48    spl4_6 <=> r2_hidden(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.48  fof(f264,plain,(
% 0.20/0.48    spl4_14),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f254])).
% 0.20/0.48  fof(f254,plain,(
% 0.20/0.48    $false | spl4_14),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f81,f252])).
% 0.20/0.48  fof(f252,plain,(
% 0.20/0.48    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | spl4_14),
% 0.20/0.48    inference(avatar_component_clause,[],[f250])).
% 0.20/0.48  fof(f250,plain,(
% 0.20/0.48    spl4_14 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    ( ! [X6,X2,X0,X1] : (r2_hidden(X6,k2_enumset1(X0,X1,X2,X6))) )),
% 0.20/0.48    inference(equality_resolution,[],[f80])).
% 0.20/0.48  fof(f80,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X1] : (r2_hidden(X6,X4) | k2_enumset1(X0,X1,X2,X6) != X4) )),
% 0.20/0.48    inference(equality_resolution,[],[f51])).
% 0.20/0.48  fof(f51,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X3,X1] : (r2_hidden(X6,X4) | X3 != X6 | k2_enumset1(X0,X1,X2,X3) != X4) )),
% 0.20/0.48    inference(cnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | (((sK2(X0,X1,X2,X3,X4) != X3 & sK2(X0,X1,X2,X3,X4) != X2 & sK2(X0,X1,X2,X3,X4) != X1 & sK2(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4),X4)) & (sK2(X0,X1,X2,X3,X4) = X3 | sK2(X0,X1,X2,X3,X4) = X2 | sK2(X0,X1,X2,X3,X4) = X1 | sK2(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK2(X0,X1,X2,X3,X4),X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f28,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ! [X4,X3,X2,X1,X0] : (? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4))) => (((sK2(X0,X1,X2,X3,X4) != X3 & sK2(X0,X1,X2,X3,X4) != X2 & sK2(X0,X1,X2,X3,X4) != X1 & sK2(X0,X1,X2,X3,X4) != X0) | ~r2_hidden(sK2(X0,X1,X2,X3,X4),X4)) & (sK2(X0,X1,X2,X3,X4) = X3 | sK2(X0,X1,X2,X3,X4) = X2 | sK2(X0,X1,X2,X3,X4) = X1 | sK2(X0,X1,X2,X3,X4) = X0 | r2_hidden(sK2(X0,X1,X2,X3,X4),X4))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X6] : ((r2_hidden(X6,X4) | (X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.20/0.48    inference(rectify,[],[f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5 | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.20/0.48    inference(flattening,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : ((k2_enumset1(X0,X1,X2,X3) = X4 | ? [X5] : (((X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5) | ~r2_hidden(X5,X4)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | r2_hidden(X5,X4)))) & (! [X5] : ((r2_hidden(X5,X4) | (X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)) & ((X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5) | ~r2_hidden(X5,X4))) | k2_enumset1(X0,X1,X2,X3) != X4))),
% 0.20/0.48    inference(nnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> (X3 = X5 | X2 = X5 | X1 = X5 | X0 = X5)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : (k2_enumset1(X0,X1,X2,X3) = X4 <=> ! [X5] : (r2_hidden(X5,X4) <=> ~(X3 != X5 & X2 != X5 & X1 != X5 & X0 != X5)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_enumset1)).
% 0.20/0.48  fof(f253,plain,(
% 0.20/0.48    ~spl4_14 | ~spl4_10 | spl4_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f231,f209,f201,f250])).
% 0.20/0.48  fof(f209,plain,(
% 0.20/0.48    spl4_11 <=> r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.48  fof(f231,plain,(
% 0.20/0.48    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | (~spl4_10 | spl4_11)),
% 0.20/0.48    inference(superposition,[],[f211,f203])).
% 0.20/0.48  fof(f203,plain,(
% 0.20/0.48    sK0 = sK1 | ~spl4_10),
% 0.20/0.48    inference(avatar_component_clause,[],[f201])).
% 0.20/0.48  fof(f211,plain,(
% 0.20/0.48    ~r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl4_11),
% 0.20/0.48    inference(avatar_component_clause,[],[f209])).
% 0.20/0.48  fof(f221,plain,(
% 0.20/0.48    ~spl4_1 | ~spl4_2 | spl4_8 | spl4_9),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f216])).
% 0.20/0.48  fof(f216,plain,(
% 0.20/0.48    $false | (~spl4_1 | ~spl4_2 | spl4_8 | spl4_9)),
% 0.20/0.48    inference(unit_resulting_resolution,[],[f98,f103,f194,f199,f175])).
% 0.20/0.48  fof(f175,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f174])).
% 0.20/0.48  fof(f174,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.20/0.48    inference(resolution,[],[f46,f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.48    inference(nnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    ~r1_tarski(sK1,sK0) | spl4_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f197])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    spl4_9 <=> r1_tarski(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    v3_ordinal1(sK1) | ~spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f101])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    spl4_2 <=> v3_ordinal1(sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    v3_ordinal1(sK0) | ~spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    spl4_1 <=> v3_ordinal1(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    ~spl4_11 | spl4_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f190,f106,f209])).
% 0.20/0.49  fof(f190,plain,(
% 0.20/0.49    ~r2_hidden(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl4_3),
% 0.20/0.49    inference(resolution,[],[f108,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 0.20/0.49    inference(equality_resolution,[],[f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK3(X0,X1,X2),X1) & ~r2_hidden(sK3(X0,X1,X2),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (r2_hidden(sK3(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(rectify,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(flattening,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.20/0.49    inference(nnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    ~r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1))) | spl4_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f106])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    ~spl4_9 | spl4_10 | ~spl4_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f188,f183,f201,f197])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    spl4_7 <=> r1_tarski(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    sK0 = sK1 | ~r1_tarski(sK1,sK0) | ~spl4_7),
% 0.20/0.49    inference(resolution,[],[f185,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(flattening,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.49    inference(nnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1) | ~spl4_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f183])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    ~spl4_8 | spl4_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f189,f106,f192])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    ~r2_hidden(sK0,sK1) | spl4_3),
% 0.20/0.49    inference(resolution,[],[f108,f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f35])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    ~spl4_1 | ~spl4_2 | spl4_7 | ~spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f181,f110,f183,f101,f96])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    spl4_4 <=> r1_ordinal1(sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~spl4_4),
% 0.20/0.49    inference(resolution,[],[f111,f44])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    r1_ordinal1(sK0,sK1) | ~spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f110])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    ~spl4_1 | ~spl4_2 | spl4_6 | spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f173,f110,f177,f101,f96])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    r2_hidden(sK1,sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl4_4),
% 0.20/0.49    inference(resolution,[],[f46,f112])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    ~r1_ordinal1(sK0,sK1) | spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f110])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl4_3 | spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f76,f110,f106])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.20/0.49    inference(definition_unfolding,[],[f42,f74])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f11])).
% 0.20/0.49  fof(f11,conjecture,(
% 0.20/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    ~spl4_3 | ~spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f75,f110,f106])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k2_enumset1(sK1,sK1,sK1,sK1)))),
% 0.20/0.49    inference(definition_unfolding,[],[f43,f74])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f41,f101])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    v3_ordinal1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    spl4_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f40,f96])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    v3_ordinal1(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (6786)------------------------------
% 0.20/0.49  % (6786)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (6786)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (6786)Memory used [KB]: 10874
% 0.20/0.49  % (6786)Time elapsed: 0.079 s
% 0.20/0.49  % (6786)------------------------------
% 0.20/0.49  % (6786)------------------------------
% 0.20/0.49  % (6762)Success in time 0.13 s
%------------------------------------------------------------------------------

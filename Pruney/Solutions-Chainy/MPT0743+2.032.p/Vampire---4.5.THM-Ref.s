%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  147 ( 332 expanded)
%              Number of leaves         :   29 ( 118 expanded)
%              Depth                    :   12
%              Number of atoms          :  473 (1099 expanded)
%              Number of equality atoms :   36 ( 114 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f402,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f99,f108,f109,f150,f156,f162,f166,f176,f181,f257,f277,f342,f349,f362,f366,f388,f397,f401])).

fof(f401,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_9
    | spl3_16 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_9
    | spl3_16 ),
    inference(unit_resulting_resolution,[],[f98,f93,f175,f340,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f51,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f340,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl3_16
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f175,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_9 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl3_9
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f93,plain,
    ( v3_ordinal1(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f98,plain,
    ( v3_ordinal1(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl3_2
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f397,plain,(
    spl3_19 ),
    inference(avatar_contradiction_clause,[],[f392])).

fof(f392,plain,
    ( $false
    | spl3_19 ),
    inference(unit_resulting_resolution,[],[f88,f387,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f62,f71])).

fof(f71,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f68,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f387,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl3_19
  <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f88,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f388,plain,
    ( ~ spl3_19
    | spl3_10
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f374,f359,f178,f385])).

fof(f178,plain,
    ( spl3_10
  <=> r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f359,plain,
    ( spl3_18
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f374,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))
    | spl3_10
    | ~ spl3_18 ),
    inference(superposition,[],[f180,f361])).

fof(f361,plain,
    ( sK0 = sK1
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f359])).

fof(f180,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f178])).

fof(f366,plain,
    ( ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2
    | spl3_3
    | spl3_17 ),
    inference(unit_resulting_resolution,[],[f93,f98,f103,f357,f138])).

fof(f357,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl3_17 ),
    inference(avatar_component_clause,[],[f355])).

fof(f355,plain,
    ( spl3_17
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f103,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f362,plain,
    ( ~ spl3_17
    | spl3_18
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f347,f339,f359,f355])).

fof(f347,plain,
    ( sK0 = sK1
    | ~ r1_tarski(sK1,sK0)
    | ~ spl3_16 ),
    inference(resolution,[],[f341,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f341,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f339])).

fof(f349,plain,
    ( ~ spl3_9
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f345])).

fof(f345,plain,
    ( $false
    | ~ spl3_9
    | ~ spl3_16 ),
    inference(unit_resulting_resolution,[],[f174,f341,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f174,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f173])).

fof(f342,plain,
    ( ~ spl3_2
    | ~ spl3_1
    | spl3_16
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f334,f101,f339,f91,f96])).

fof(f334,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f318,f102])).

fof(f102,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f101])).

fof(f318,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X5,X4)
      | r1_tarski(X5,X4)
      | ~ v3_ordinal1(X5)
      | ~ v3_ordinal1(X4) ) ),
    inference(resolution,[],[f147,f61])).

fof(f147,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f126,f48])).

fof(f126,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r1_tarski(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(resolution,[],[f50,f48])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f277,plain,
    ( ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(unit_resulting_resolution,[],[f102,f179,f113])).

fof(f113,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k1_enumset1(X2,X2,X2))
      | ~ r2_hidden(X2,X3) ) ),
    inference(resolution,[],[f83,f61])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f71])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f179,plain,
    ( r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f178])).

fof(f257,plain,
    ( ~ spl3_7
    | spl3_9
    | spl3_10 ),
    inference(avatar_contradiction_clause,[],[f253])).

fof(f253,plain,
    ( $false
    | ~ spl3_7
    | spl3_9
    | spl3_10 ),
    inference(unit_resulting_resolution,[],[f175,f180,f155,f87])).

fof(f87,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1)))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f55,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f67,f69])).

fof(f67,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f55,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
              & ~ r2_hidden(sK2(X0,X1,X2),X0) )
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( r2_hidden(sK2(X0,X1,X2),X1)
            | r2_hidden(sK2(X0,X1,X2),X0)
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            & ~ r2_hidden(sK2(X0,X1,X2),X0) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( r2_hidden(sK2(X0,X1,X2),X1)
          | r2_hidden(sK2(X0,X1,X2),X0)
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f155,plain,
    ( r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_7
  <=> r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f181,plain,
    ( ~ spl3_10
    | spl3_7 ),
    inference(avatar_split_clause,[],[f168,f153,f178])).

fof(f168,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0))
    | spl3_7 ),
    inference(resolution,[],[f154,f85])).

fof(f85,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f57,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f154,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f153])).

fof(f176,plain,
    ( ~ spl3_9
    | spl3_7 ),
    inference(avatar_split_clause,[],[f167,f153,f173])).

fof(f167,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl3_7 ),
    inference(resolution,[],[f154,f86])).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k3_tarski(k1_enumset1(X0,X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f56,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f166,plain,
    ( ~ spl3_7
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f165,f159,f153])).

fof(f159,plain,
    ( spl3_8
  <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f165,plain,
    ( ~ r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | ~ spl3_8 ),
    inference(resolution,[],[f161,f61])).

fof(f161,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f159])).

fof(f162,plain,
    ( ~ spl3_5
    | ~ spl3_2
    | spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f157,f105,f159,f96,f128])).

fof(f128,plain,
    ( spl3_5
  <=> v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f105,plain,
    ( spl3_4
  <=> r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f157,plain,
    ( r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | ~ spl3_4 ),
    inference(resolution,[],[f106,f48])).

fof(f106,plain,
    ( r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f156,plain,
    ( ~ spl3_5
    | ~ spl3_2
    | spl3_7
    | spl3_4 ),
    inference(avatar_split_clause,[],[f136,f105,f153,f96,f128])).

fof(f136,plain,
    ( r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | spl3_4 ),
    inference(resolution,[],[f51,f107])).

fof(f107,plain,
    ( ~ r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f105])).

fof(f150,plain,
    ( ~ spl3_1
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl3_1
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f93,f130,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v3_ordinal1(k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0))))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f52,f72])).

fof(f72,plain,(
    ! [X0] : k1_ordinal1(X0) = k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0))) ),
    inference(definition_unfolding,[],[f53,f70,f71])).

fof(f53,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f52,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f130,plain,
    ( ~ v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f109,plain,
    ( spl3_3
    | spl3_4 ),
    inference(avatar_split_clause,[],[f74,f105,f101])).

fof(f74,plain,
    ( r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f46,f72])).

fof(f46,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
      | ~ r2_hidden(sK0,sK1) )
    & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
      | r2_hidden(sK0,sK1) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).

fof(f32,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
            | ~ r2_hidden(sK0,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK0),X1)
            | r2_hidden(sK0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK0),X1)
          | ~ r2_hidden(sK0,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK0),X1)
          | r2_hidden(sK0,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
        | ~ r2_hidden(sK0,sK1) )
      & ( r1_ordinal1(k1_ordinal1(sK0),sK1)
        | r2_hidden(sK0,sK1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

% (24822)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f108,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f73,f105,f101])).

fof(f73,plain,
    ( ~ r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f47,f72])).

fof(f47,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f99,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f45,f96])).

fof(f45,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f44,f91])).

fof(f44,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:09:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (24816)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.50  % (24819)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.50  % (24832)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.50  % (24807)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.50  % (24824)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (24832)Refutation not found, incomplete strategy% (24832)------------------------------
% 0.21/0.51  % (24832)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24811)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (24827)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (24827)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (24814)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (24804)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (24833)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (24808)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (24825)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (24832)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24832)Memory used [KB]: 10746
% 0.21/0.53  % (24832)Time elapsed: 0.112 s
% 0.21/0.53  % (24832)------------------------------
% 0.21/0.53  % (24832)------------------------------
% 0.21/0.53  % (24828)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (24806)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (24805)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (24810)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (24830)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (24831)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f402,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f94,f99,f108,f109,f150,f156,f162,f166,f176,f181,f257,f277,f342,f349,f362,f366,f388,f397,f401])).
% 0.21/0.54  fof(f401,plain,(
% 0.21/0.54    ~spl3_1 | ~spl3_2 | spl3_9 | spl3_16),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f398])).
% 0.21/0.54  fof(f398,plain,(
% 0.21/0.54    $false | (~spl3_1 | ~spl3_2 | spl3_9 | spl3_16)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f98,f93,f175,f340,f138])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f137])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.21/0.54    inference(resolution,[],[f51,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f23])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f26])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.21/0.54  fof(f340,plain,(
% 0.21/0.54    ~r1_tarski(sK0,sK1) | spl3_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f339])).
% 0.21/0.54  fof(f339,plain,(
% 0.21/0.54    spl3_16 <=> r1_tarski(sK0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.54  fof(f175,plain,(
% 0.21/0.54    ~r2_hidden(sK1,sK0) | spl3_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f173])).
% 0.21/0.54  fof(f173,plain,(
% 0.21/0.54    spl3_9 <=> r2_hidden(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.54  fof(f93,plain,(
% 0.21/0.54    v3_ordinal1(sK0) | ~spl3_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f91])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    spl3_1 <=> v3_ordinal1(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.54  fof(f98,plain,(
% 0.21/0.54    v3_ordinal1(sK1) | ~spl3_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    spl3_2 <=> v3_ordinal1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.54  fof(f397,plain,(
% 0.21/0.54    spl3_19),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f392])).
% 0.21/0.54  fof(f392,plain,(
% 0.21/0.54    $false | spl3_19),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f88,f387,f84])).
% 0.21/0.54  fof(f84,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f62,f71])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f68,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.54    inference(nnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.54  fof(f387,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | spl3_19),
% 0.21/0.54    inference(avatar_component_clause,[],[f385])).
% 0.21/0.54  fof(f385,plain,(
% 0.21/0.54    spl3_19 <=> r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f65])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(flattening,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.21/0.54    inference(nnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f388,plain,(
% 0.21/0.54    ~spl3_19 | spl3_10 | ~spl3_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f374,f359,f178,f385])).
% 0.21/0.54  fof(f178,plain,(
% 0.21/0.54    spl3_10 <=> r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.54  fof(f359,plain,(
% 0.21/0.54    spl3_18 <=> sK0 = sK1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.54  fof(f374,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k1_enumset1(sK0,sK0,sK0)) | (spl3_10 | ~spl3_18)),
% 0.21/0.54    inference(superposition,[],[f180,f361])).
% 0.21/0.54  fof(f361,plain,(
% 0.21/0.54    sK0 = sK1 | ~spl3_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f359])).
% 0.21/0.54  fof(f180,plain,(
% 0.21/0.54    ~r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0)) | spl3_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f178])).
% 0.21/0.54  fof(f366,plain,(
% 0.21/0.54    ~spl3_1 | ~spl3_2 | spl3_3 | spl3_17),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f363])).
% 0.21/0.54  fof(f363,plain,(
% 0.21/0.54    $false | (~spl3_1 | ~spl3_2 | spl3_3 | spl3_17)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f93,f98,f103,f357,f138])).
% 0.21/0.54  fof(f357,plain,(
% 0.21/0.54    ~r1_tarski(sK1,sK0) | spl3_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f355])).
% 0.21/0.54  fof(f355,plain,(
% 0.21/0.54    spl3_17 <=> r1_tarski(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.54  fof(f103,plain,(
% 0.21/0.54    ~r2_hidden(sK0,sK1) | spl3_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f101])).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    spl3_3 <=> r2_hidden(sK0,sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.54  fof(f362,plain,(
% 0.21/0.54    ~spl3_17 | spl3_18 | ~spl3_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f347,f339,f359,f355])).
% 0.21/0.54  fof(f347,plain,(
% 0.21/0.54    sK0 = sK1 | ~r1_tarski(sK1,sK0) | ~spl3_16),
% 0.21/0.54    inference(resolution,[],[f341,f66])).
% 0.21/0.54  fof(f66,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f43])).
% 0.21/0.54  fof(f341,plain,(
% 0.21/0.54    r1_tarski(sK0,sK1) | ~spl3_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f339])).
% 0.21/0.54  fof(f349,plain,(
% 0.21/0.54    ~spl3_9 | ~spl3_16),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f345])).
% 0.21/0.54  fof(f345,plain,(
% 0.21/0.54    $false | (~spl3_9 | ~spl3_16)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f174,f341,f61])).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,axiom,(
% 0.21/0.54    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.54  fof(f174,plain,(
% 0.21/0.54    r2_hidden(sK1,sK0) | ~spl3_9),
% 0.21/0.54    inference(avatar_component_clause,[],[f173])).
% 0.21/0.54  fof(f342,plain,(
% 0.21/0.54    ~spl3_2 | ~spl3_1 | spl3_16 | ~spl3_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f334,f101,f339,f91,f96])).
% 0.21/0.54  fof(f334,plain,(
% 0.21/0.54    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | ~spl3_3),
% 0.21/0.54    inference(resolution,[],[f318,f102])).
% 0.21/0.54  fof(f102,plain,(
% 0.21/0.54    r2_hidden(sK0,sK1) | ~spl3_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f101])).
% 0.21/0.54  fof(f318,plain,(
% 0.21/0.54    ( ! [X4,X5] : (~r2_hidden(X5,X4) | r1_tarski(X5,X4) | ~v3_ordinal1(X5) | ~v3_ordinal1(X4)) )),
% 0.21/0.54    inference(resolution,[],[f147,f61])).
% 0.21/0.54  fof(f147,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f146])).
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | r1_tarski(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.21/0.54    inference(resolution,[],[f126,f48])).
% 0.21/0.54  fof(f126,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X1,X0)) )),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f123])).
% 0.21/0.54  fof(f123,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r1_tarski(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 0.21/0.54    inference(resolution,[],[f50,f48])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,axiom,(
% 0.21/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 0.21/0.54  fof(f277,plain,(
% 0.21/0.54    ~spl3_3 | ~spl3_10),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f275])).
% 0.21/0.54  fof(f275,plain,(
% 0.21/0.54    $false | (~spl3_3 | ~spl3_10)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f102,f179,f113])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ( ! [X2,X3] : (~r2_hidden(X3,k1_enumset1(X2,X2,X2)) | ~r2_hidden(X2,X3)) )),
% 0.21/0.54    inference(resolution,[],[f83,f61])).
% 0.21/0.54  fof(f83,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f63,f71])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f41])).
% 0.21/0.54  fof(f179,plain,(
% 0.21/0.54    r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0)) | ~spl3_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f178])).
% 0.21/0.54  fof(f257,plain,(
% 0.21/0.54    ~spl3_7 | spl3_9 | spl3_10),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f253])).
% 0.21/0.54  fof(f253,plain,(
% 0.21/0.54    $false | (~spl3_7 | spl3_9 | spl3_10)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f175,f180,f155,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1))) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 0.21/0.54    inference(definition_unfolding,[],[f55,f70])).
% 0.21/0.54  fof(f70,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f67,f69])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f38,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.54    inference(rectify,[],[f37])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.54    inference(flattening,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.54    inference(nnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.54  fof(f155,plain,(
% 0.21/0.54    r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | ~spl3_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f153])).
% 0.21/0.54  fof(f153,plain,(
% 0.21/0.54    spl3_7 <=> r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.54  fof(f181,plain,(
% 0.21/0.54    ~spl3_10 | spl3_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f168,f153,f178])).
% 0.21/0.54  fof(f168,plain,(
% 0.21/0.54    ~r2_hidden(sK1,k1_enumset1(sK0,sK0,sK0)) | spl3_7),
% 0.21/0.54    inference(resolution,[],[f154,f85])).
% 0.21/0.54  fof(f85,plain,(
% 0.21/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1))) | ~r2_hidden(X4,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f80])).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 0.21/0.54    inference(definition_unfolding,[],[f57,f70])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f154,plain,(
% 0.21/0.54    ~r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | spl3_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f153])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    ~spl3_9 | spl3_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f167,f153,f173])).
% 0.21/0.54  fof(f167,plain,(
% 0.21/0.54    ~r2_hidden(sK1,sK0) | spl3_7),
% 0.21/0.54    inference(resolution,[],[f154,f86])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_tarski(k1_enumset1(X0,X0,X1))) | ~r2_hidden(X4,X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f81])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k3_tarski(k1_enumset1(X0,X0,X1)) != X2) )),
% 0.21/0.54    inference(definition_unfolding,[],[f56,f70])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f166,plain,(
% 0.21/0.54    ~spl3_7 | ~spl3_8),
% 0.21/0.54    inference(avatar_split_clause,[],[f165,f159,f153])).
% 0.21/0.54  fof(f159,plain,(
% 0.21/0.54    spl3_8 <=> r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.54  fof(f165,plain,(
% 0.21/0.54    ~r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | ~spl3_8),
% 0.21/0.54    inference(resolution,[],[f161,f61])).
% 0.21/0.54  fof(f161,plain,(
% 0.21/0.54    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) | ~spl3_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f159])).
% 0.21/0.54  fof(f162,plain,(
% 0.21/0.54    ~spl3_5 | ~spl3_2 | spl3_8 | ~spl3_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f157,f105,f159,f96,f128])).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    spl3_5 <=> v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.54  fof(f105,plain,(
% 0.21/0.54    spl3_4 <=> r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.54  fof(f157,plain,(
% 0.21/0.54    r1_tarski(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | ~spl3_4),
% 0.21/0.54    inference(resolution,[],[f106,f48])).
% 0.21/0.54  fof(f106,plain,(
% 0.21/0.54    r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) | ~spl3_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f105])).
% 0.21/0.54  fof(f156,plain,(
% 0.21/0.54    ~spl3_5 | ~spl3_2 | spl3_7 | spl3_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f136,f105,f153,f96,f128])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    r2_hidden(sK1,k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | ~v3_ordinal1(sK1) | ~v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | spl3_4),
% 0.21/0.54    inference(resolution,[],[f51,f107])).
% 0.21/0.54  fof(f107,plain,(
% 0.21/0.54    ~r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) | spl3_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f105])).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    ~spl3_1 | spl3_5),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f148])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    $false | (~spl3_1 | spl3_5)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f93,f130,f75])).
% 0.21/0.54  fof(f75,plain,(
% 0.21/0.54    ( ! [X0] : (v3_ordinal1(k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(definition_unfolding,[],[f52,f72])).
% 0.21/0.54  fof(f72,plain,(
% 0.21/0.54    ( ! [X0] : (k1_ordinal1(X0) = k3_tarski(k1_enumset1(X0,X0,k1_enumset1(X0,X0,X0)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f53,f70,f71])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,axiom,(
% 0.21/0.54    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,axiom,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.21/0.54  fof(f130,plain,(
% 0.21/0.54    ~v3_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0)))) | spl3_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f128])).
% 0.21/0.54  fof(f109,plain,(
% 0.21/0.54    spl3_3 | spl3_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f74,f105,f101])).
% 0.21/0.54  fof(f74,plain,(
% 0.21/0.54    r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(definition_unfolding,[],[f46,f72])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f31,f33,f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK0),X1) | ~r2_hidden(sK0,X1)) & (r1_ordinal1(k1_ordinal1(sK0),X1) | r2_hidden(sK0,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)) & (r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)) & v3_ordinal1(sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  % (24822)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(flattening,[],[f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f21])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.54    inference(negated_conjecture,[],[f19])).
% 0.21/0.54  fof(f19,conjecture,(
% 0.21/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    ~spl3_3 | ~spl3_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f73,f105,f101])).
% 0.21/0.54  fof(f73,plain,(
% 0.21/0.54    ~r1_ordinal1(k3_tarski(k1_enumset1(sK0,sK0,k1_enumset1(sK0,sK0,sK0))),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(definition_unfolding,[],[f47,f72])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f99,plain,(
% 0.21/0.54    spl3_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f45,f96])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    v3_ordinal1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    spl3_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f44,f91])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    v3_ordinal1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f34])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (24827)------------------------------
% 0.21/0.54  % (24827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24827)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (24827)Memory used [KB]: 10874
% 0.21/0.54  % (24827)Time elapsed: 0.124 s
% 0.21/0.54  % (24827)------------------------------
% 0.21/0.54  % (24827)------------------------------
% 0.21/0.54  % (24821)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (24803)Success in time 0.191 s
%------------------------------------------------------------------------------

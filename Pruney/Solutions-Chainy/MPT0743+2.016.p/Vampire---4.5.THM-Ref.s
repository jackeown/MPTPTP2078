%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 199 expanded)
%              Number of leaves         :   24 (  67 expanded)
%              Depth                    :   13
%              Number of atoms          :  373 ( 736 expanded)
%              Number of equality atoms :   10 (  29 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (24185)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
fof(f311,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f82,f111,f113,f116,f149,f165,f239,f303,f310])).

fof(f310,plain,
    ( ~ spl5_1
    | ~ spl5_9 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_9 ),
    inference(resolution,[],[f305,f75])).

fof(f75,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_1
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f305,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl5_9 ),
    inference(resolution,[],[f302,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f45])).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f302,plain,
    ( r2_hidden(sK2,k2_tarski(sK1,sK1))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f300])).

fof(f300,plain,
    ( spl5_9
  <=> r2_hidden(sK2,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f303,plain,
    ( spl5_9
    | spl5_7
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f273,f162,f227,f300])).

fof(f227,plain,
    ( spl5_7
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f162,plain,
    ( spl5_6
  <=> r2_hidden(sK2,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f273,plain,
    ( r2_hidden(sK2,sK1)
    | r2_hidden(sK2,k2_tarski(sK1,sK1))
    | ~ spl5_6 ),
    inference(resolution,[],[f144,f164])).

fof(f164,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f162])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f58,f72])).

fof(f72,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_xboole_0(X0,X1)) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f3,f22])).

fof(f22,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f58,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | r2_hidden(X4,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
              & ~ r2_hidden(sK4(X0,X1,X2),X1) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X3,X1) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X0)
            | r2_hidden(X3,X1)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X0)
            & ~ r2_hidden(sK4(X0,X1,X2),X1) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ( ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X3,X1) )
              | ~ r2_hidden(X3,X2) )
            & ( r2_hidden(X3,X0)
              | r2_hidden(X3,X1)
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X0)
                & ~ r2_hidden(X4,X1) ) )
            & ( r2_hidden(X4,X0)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f239,plain,
    ( ~ spl5_1
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(resolution,[],[f229,f152])).

fof(f152,plain,
    ( ~ r2_hidden(sK2,sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f75,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f229,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f227])).

fof(f165,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | spl5_2 ),
    inference(avatar_split_clause,[],[f160,f78,f162,f104,f100])).

fof(f100,plain,
    ( spl5_3
  <=> v3_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f104,plain,
    ( spl5_4
  <=> v3_ordinal1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f78,plain,
    ( spl5_2
  <=> r1_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f160,plain,
    ( r2_hidden(sK2,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
    | spl5_2 ),
    inference(resolution,[],[f80,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f80,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f149,plain,
    ( spl5_1
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl5_1
    | ~ spl5_5 ),
    inference(resolution,[],[f140,f76])).

fof(f76,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f140,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f137,f119])).

fof(f119,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
        | r2_hidden(X0,sK2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f110,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f110,plain,
    ( r1_tarski(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl5_5
  <=> r1_tarski(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f137,plain,(
    ! [X6,X5] : r2_hidden(X5,k2_xboole_0(X6,k2_tarski(X5,X5))) ),
    inference(resolution,[],[f126,f89])).

fof(f89,plain,(
    ! [X2] : r2_hidden(X2,k2_tarski(X2,X2)) ),
    inference(resolution,[],[f71,f85])).

fof(f85,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f54,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f55,f45])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(X0,k2_xboole_0(X2,X1)) ) ),
    inference(resolution,[],[f60,f72])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | r2_hidden(X4,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f116,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl5_3 ),
    inference(resolution,[],[f114,f41])).

fof(f41,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r1_ordinal1(k1_ordinal1(sK1),sK2)
      | ~ r2_hidden(sK1,sK2) )
    & ( r1_ordinal1(k1_ordinal1(sK1),sK2)
      | r2_hidden(sK1,sK2) )
    & v3_ordinal1(sK2)
    & v3_ordinal1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
              | ~ r2_hidden(X0,X1) )
            & ( r1_ordinal1(k1_ordinal1(X0),X1)
              | r2_hidden(X0,X1) )
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(sK1),X1)
            | ~ r2_hidden(sK1,X1) )
          & ( r1_ordinal1(k1_ordinal1(sK1),X1)
            | r2_hidden(sK1,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ( ~ r1_ordinal1(k1_ordinal1(sK1),X1)
          | ~ r2_hidden(sK1,X1) )
        & ( r1_ordinal1(k1_ordinal1(sK1),X1)
          | r2_hidden(sK1,X1) )
        & v3_ordinal1(X1) )
   => ( ( ~ r1_ordinal1(k1_ordinal1(sK1),sK2)
        | ~ r2_hidden(sK1,sK2) )
      & ( r1_ordinal1(k1_ordinal1(sK1),sK2)
        | r2_hidden(sK1,sK2) )
      & v3_ordinal1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(k1_ordinal1(X0),X1)
            | ~ r2_hidden(X0,X1) )
          & ( r1_ordinal1(k1_ordinal1(X0),X1)
            | r2_hidden(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

% (24183)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f114,plain,
    ( ~ v3_ordinal1(sK1)
    | spl5_3 ),
    inference(resolution,[],[f102,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f47,f66])).

fof(f66,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f46,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f47,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f102,plain,
    ( ~ v3_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f100])).

fof(f113,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f106,f42])).

fof(f42,plain,(
    v3_ordinal1(sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f106,plain,
    ( ~ v3_ordinal1(sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f104])).

fof(f111,plain,
    ( ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f96,f78,f108,f104,f100])).

fof(f96,plain,
    ( r1_tarski(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2)
    | ~ v3_ordinal1(sK2)
    | ~ v3_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1)))
    | ~ spl5_2 ),
    inference(resolution,[],[f50,f79])).

fof(f79,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f82,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f68,f78,f74])).

fof(f68,plain,
    ( r1_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(definition_unfolding,[],[f43,f66])).

fof(f43,plain,
    ( r1_ordinal1(k1_ordinal1(sK1),sK2)
    | r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f81,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f67,f78,f74])).

fof(f67,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(definition_unfolding,[],[f44,f66])).

fof(f44,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK1),sK2)
    | ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

% (24186)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:40:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (24208)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.52  % (24200)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.52  % (24194)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (24193)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (24194)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % (24184)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  % (24185)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.53  fof(f311,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f81,f82,f111,f113,f116,f149,f165,f239,f303,f310])).
% 0.22/0.53  fof(f310,plain,(
% 0.22/0.53    ~spl5_1 | ~spl5_9),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f309])).
% 0.22/0.53  fof(f309,plain,(
% 0.22/0.53    $false | (~spl5_1 | ~spl5_9)),
% 0.22/0.53    inference(resolution,[],[f305,f75])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    r2_hidden(sK1,sK2) | ~spl5_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    spl5_1 <=> r2_hidden(sK1,sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.53  fof(f305,plain,(
% 0.22/0.53    ~r2_hidden(sK1,sK2) | ~spl5_9),
% 0.22/0.53    inference(resolution,[],[f302,f87])).
% 0.22/0.53  fof(f87,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X0)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(resolution,[],[f70,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,axiom,(
% 0.22/0.53    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f56,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.53  fof(f302,plain,(
% 0.22/0.53    r2_hidden(sK2,k2_tarski(sK1,sK1)) | ~spl5_9),
% 0.22/0.53    inference(avatar_component_clause,[],[f300])).
% 0.22/0.53  fof(f300,plain,(
% 0.22/0.53    spl5_9 <=> r2_hidden(sK2,k2_tarski(sK1,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.53  fof(f303,plain,(
% 0.22/0.53    spl5_9 | spl5_7 | ~spl5_6),
% 0.22/0.53    inference(avatar_split_clause,[],[f273,f162,f227,f300])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    spl5_7 <=> r2_hidden(sK2,sK1)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.53  fof(f162,plain,(
% 0.22/0.53    spl5_6 <=> r2_hidden(sK2,k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.53  fof(f273,plain,(
% 0.22/0.53    r2_hidden(sK2,sK1) | r2_hidden(sK2,k2_tarski(sK1,sK1)) | ~spl5_6),
% 0.22/0.53    inference(resolution,[],[f144,f164])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    r2_hidden(sK2,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) | ~spl5_6),
% 0.22/0.53    inference(avatar_component_clause,[],[f162])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 0.22/0.53    inference(resolution,[],[f58,f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP0(X1,X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f40])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 0.22/0.53    inference(definition_folding,[],[f3,f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | r2_hidden(X4,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((~r2_hidden(sK4(X0,X1,X2),X0) & ~r2_hidden(sK4(X0,X1,X2),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X0) & ~r2_hidden(sK4(X0,X1,X2),X1)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((~r2_hidden(X3,X0) & ~r2_hidden(X3,X1)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X0) & ~r2_hidden(X4,X1))) & (r2_hidden(X4,X0) | r2_hidden(X4,X1) | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 0.22/0.53    inference(rectify,[],[f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.53    inference(flattening,[],[f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 0.22/0.53    inference(nnf_transformation,[],[f22])).
% 0.22/0.53  fof(f239,plain,(
% 0.22/0.53    ~spl5_1 | ~spl5_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f235])).
% 0.22/0.53  fof(f235,plain,(
% 0.22/0.53    $false | (~spl5_1 | ~spl5_7)),
% 0.22/0.53    inference(resolution,[],[f229,f152])).
% 0.22/0.53  fof(f152,plain,(
% 0.22/0.53    ~r2_hidden(sK2,sK1) | ~spl5_1),
% 0.22/0.53    inference(resolution,[],[f75,f49])).
% 0.22/0.53  fof(f49,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.22/0.53  fof(f229,plain,(
% 0.22/0.53    r2_hidden(sK2,sK1) | ~spl5_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f227])).
% 0.22/0.53  fof(f165,plain,(
% 0.22/0.53    ~spl5_3 | ~spl5_4 | spl5_6 | spl5_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f160,f78,f162,f104,f100])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    spl5_3 <=> v3_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    spl5_4 <=> v3_ordinal1(sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    spl5_2 <=> r1_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    r2_hidden(sK2,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) | ~v3_ordinal1(sK2) | ~v3_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1))) | spl5_2),
% 0.22/0.53    inference(resolution,[],[f80,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ~r1_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2) | spl5_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f78])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    spl5_1 | ~spl5_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f145])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    $false | (spl5_1 | ~spl5_5)),
% 0.22/0.53    inference(resolution,[],[f140,f76])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ~r2_hidden(sK1,sK2) | spl5_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f74])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    r2_hidden(sK1,sK2) | ~spl5_5),
% 0.22/0.53    inference(resolution,[],[f137,f119])).
% 0.22/0.53  fof(f119,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k2_xboole_0(sK1,k2_tarski(sK1,sK1))) | r2_hidden(X0,sK2)) ) | ~spl5_5),
% 0.22/0.53    inference(resolution,[],[f110,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X3,X0) | r2_hidden(X3,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(rectify,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.53    inference(nnf_transformation,[],[f20])).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    r1_tarski(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2) | ~spl5_5),
% 0.22/0.53    inference(avatar_component_clause,[],[f108])).
% 0.22/0.53  fof(f108,plain,(
% 0.22/0.53    spl5_5 <=> r1_tarski(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    ( ! [X6,X5] : (r2_hidden(X5,k2_xboole_0(X6,k2_tarski(X5,X5)))) )),
% 0.22/0.53    inference(resolution,[],[f126,f89])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    ( ! [X2] : (r2_hidden(X2,k2_tarski(X2,X2))) )),
% 0.22/0.53    inference(resolution,[],[f71,f85])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f84])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 0.22/0.53    inference(resolution,[],[f54,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f33])).
% 0.22/0.54  fof(f71,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(k2_tarski(X0,X0),X1) | r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f55,f45])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f34])).
% 0.22/0.54  fof(f126,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(X0,k2_xboole_0(X2,X1))) )),
% 0.22/0.54    inference(resolution,[],[f60,f72])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X0) | r2_hidden(X4,X2)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f39])).
% 0.22/0.54  fof(f116,plain,(
% 0.22/0.54    spl5_3),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f115])).
% 0.22/0.54  fof(f115,plain,(
% 0.22/0.54    $false | spl5_3),
% 0.22/0.54    inference(resolution,[],[f114,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    v3_ordinal1(sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ((~r1_ordinal1(k1_ordinal1(sK1),sK2) | ~r2_hidden(sK1,sK2)) & (r1_ordinal1(k1_ordinal1(sK1),sK2) | r2_hidden(sK1,sK2)) & v3_ordinal1(sK2)) & v3_ordinal1(sK1)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f25,f27,f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(k1_ordinal1(sK1),X1) | ~r2_hidden(sK1,X1)) & (r1_ordinal1(k1_ordinal1(sK1),X1) | r2_hidden(sK1,X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK1))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ? [X1] : ((~r1_ordinal1(k1_ordinal1(sK1),X1) | ~r2_hidden(sK1,X1)) & (r1_ordinal1(k1_ordinal1(sK1),X1) | r2_hidden(sK1,X1)) & v3_ordinal1(X1)) => ((~r1_ordinal1(k1_ordinal1(sK1),sK2) | ~r2_hidden(sK1,sK2)) & (r1_ordinal1(k1_ordinal1(sK1),sK2) | r2_hidden(sK1,sK2)) & v3_ordinal1(sK2))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (((~r1_ordinal1(k1_ordinal1(X0),X1) | ~r2_hidden(X0,X1)) & (r1_ordinal1(k1_ordinal1(X0),X1) | r2_hidden(X0,X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f13])).
% 0.22/0.54  % (24183)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f12])).
% 0.22/0.54  fof(f12,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.54    inference(negated_conjecture,[],[f11])).
% 0.22/0.54  fof(f11,conjecture,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    ~v3_ordinal1(sK1) | spl5_3),
% 0.22/0.54    inference(resolution,[],[f102,f69])).
% 0.22/0.54  fof(f69,plain,(
% 0.22/0.54    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k2_tarski(X0,X0))) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f47,f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k2_tarski(X0,X0))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f46,f45])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,axiom,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 0.22/0.54  fof(f102,plain,(
% 0.22/0.54    ~v3_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1))) | spl5_3),
% 0.22/0.54    inference(avatar_component_clause,[],[f100])).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    spl5_4),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f112])).
% 0.22/0.54  fof(f112,plain,(
% 0.22/0.54    $false | spl5_4),
% 0.22/0.54    inference(resolution,[],[f106,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    v3_ordinal1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f106,plain,(
% 0.22/0.54    ~v3_ordinal1(sK2) | spl5_4),
% 0.22/0.54    inference(avatar_component_clause,[],[f104])).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    ~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f96,f78,f108,f104,f100])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    r1_tarski(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2) | ~v3_ordinal1(sK2) | ~v3_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1))) | ~spl5_2),
% 0.22/0.54    inference(resolution,[],[f50,f79])).
% 0.22/0.54  fof(f79,plain,(
% 0.22/0.54    r1_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2) | ~spl5_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f78])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.54  fof(f82,plain,(
% 0.22/0.54    spl5_1 | spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f68,f78,f74])).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    r1_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2) | r2_hidden(sK1,sK2)),
% 0.22/0.54    inference(definition_unfolding,[],[f43,f66])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    r1_ordinal1(k1_ordinal1(sK1),sK2) | r2_hidden(sK1,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f81,plain,(
% 0.22/0.54    ~spl5_1 | ~spl5_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f67,f78,f74])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ~r1_ordinal1(k2_xboole_0(sK1,k2_tarski(sK1,sK1)),sK2) | ~r2_hidden(sK1,sK2)),
% 0.22/0.54    inference(definition_unfolding,[],[f44,f66])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ~r1_ordinal1(k1_ordinal1(sK1),sK2) | ~r2_hidden(sK1,sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  % (24186)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (24194)------------------------------
% 0.22/0.54  % (24194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24194)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (24194)Memory used [KB]: 6396
% 0.22/0.54  % (24194)Time elapsed: 0.110 s
% 0.22/0.54  % (24194)------------------------------
% 0.22/0.54  % (24194)------------------------------
% 0.22/0.55  % (24179)Success in time 0.178 s
%------------------------------------------------------------------------------

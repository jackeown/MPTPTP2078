%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:30 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 251 expanded)
%              Number of leaves         :   30 (  87 expanded)
%              Depth                    :   14
%              Number of atoms          :  568 (1171 expanded)
%              Number of equality atoms :  174 ( 327 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f257,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f112,f115,f130,f132,f148,f151,f193,f226,f237,f239,f241,f245,f249,f252,f256])).

fof(f256,plain,(
    ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f174,f253])).

fof(f253,plain,
    ( ~ r2_hidden(sK0,sK0)
    | ~ spl4_11 ),
    inference(resolution,[],[f174,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f174,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl4_11
  <=> r2_hidden(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f252,plain,
    ( spl4_13
    | spl4_9
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f250,f107,f146,f205])).

fof(f205,plain,
    ( spl4_13
  <=> r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f146,plain,
    ( spl4_9
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f107,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k2_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f250,plain,
    ( r2_hidden(sK0,sK1)
    | r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl4_1 ),
    inference(resolution,[],[f113,f94])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_xboole_0(X0,X1))
      | r2_hidden(X4,X0)
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
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

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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

fof(f113,plain,
    ( r2_hidden(sK0,k2_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f249,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_12
    | spl4_2 ),
    inference(avatar_split_clause,[],[f247,f110,f199,f121,f118])).

fof(f118,plain,
    ( spl4_3
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f121,plain,
    ( spl4_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f199,plain,
    ( spl4_12
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f110,plain,
    ( spl4_2
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f247,plain,
    ( r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | spl4_2 ),
    inference(resolution,[],[f111,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | r1_ordinal1(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X1,X0)
            | r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

fof(f111,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f245,plain,
    ( spl4_1
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f244])).

fof(f244,plain,
    ( $false
    | spl4_1
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f147,f242])).

fof(f242,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_1 ),
    inference(resolution,[],[f108,f93])).

fof(f93,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f108,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f147,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f146])).

fof(f241,plain,
    ( spl4_6
    | spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f240,f124,f138,f135])).

fof(f135,plain,
    ( spl4_6
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f138,plain,
    ( spl4_7
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f124,plain,
    ( spl4_5
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f240,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1)
    | ~ spl4_5 ),
    inference(resolution,[],[f125,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f125,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f124])).

fof(f239,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f238,f110,f124,f121,f118])).

fof(f238,plain,
    ( r1_tarski(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f114,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f114,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f110])).

fof(f237,plain,
    ( ~ spl4_9
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | ~ spl4_9
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f209,f147])).

fof(f209,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_12 ),
    inference(resolution,[],[f200,f60])).

fof(f200,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f199])).

fof(f226,plain,
    ( ~ spl4_3
    | spl4_11
    | spl4_2
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f223,f205,f110,f173,f118])).

fof(f223,plain,
    ( r2_hidden(sK0,sK0)
    | ~ v3_ordinal1(sK0)
    | spl4_2
    | ~ spl4_13 ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,
    ( r2_hidden(sK0,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK0)
    | spl4_2
    | ~ spl4_13 ),
    inference(resolution,[],[f214,f58])).

fof(f214,plain,
    ( ~ r1_ordinal1(sK0,sK0)
    | spl4_2
    | ~ spl4_13 ),
    inference(backward_demodulation,[],[f111,f212])).

fof(f212,plain,
    ( sK0 = sK1
    | ~ spl4_13 ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,
    ( sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | sK0 = sK1
    | ~ spl4_13 ),
    inference(resolution,[],[f206,f105])).

fof(f105,plain,(
    ! [X4,X2,X0,X7,X3,X1] :
      ( ~ r2_hidden(X7,k3_enumset1(X0,X1,X2,X3,X4))
      | X3 = X7
      | X2 = X7
      | X1 = X7
      | X0 = X7
      | X4 = X7 ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( X4 = X7
      | X3 = X7
      | X2 = X7
      | X1 = X7
      | X0 = X7
      | ~ r2_hidden(X7,X5)
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ( ( ( sK3(X0,X1,X2,X3,X4,X5) != X4
              & sK3(X0,X1,X2,X3,X4,X5) != X3
              & sK3(X0,X1,X2,X3,X4,X5) != X2
              & sK3(X0,X1,X2,X3,X4,X5) != X1
              & sK3(X0,X1,X2,X3,X4,X5) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) )
          & ( sK3(X0,X1,X2,X3,X4,X5) = X4
            | sK3(X0,X1,X2,X3,X4,X5) = X3
            | sK3(X0,X1,X2,X3,X4,X5) = X2
            | sK3(X0,X1,X2,X3,X4,X5) = X1
            | sK3(X0,X1,X2,X3,X4,X5) = X0
            | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).

fof(f47,plain,(
    ! [X5,X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( ( ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 )
            | ~ r2_hidden(X6,X5) )
          & ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6
            | r2_hidden(X6,X5) ) )
     => ( ( ( sK3(X0,X1,X2,X3,X4,X5) != X4
            & sK3(X0,X1,X2,X3,X4,X5) != X3
            & sK3(X0,X1,X2,X3,X4,X5) != X2
            & sK3(X0,X1,X2,X3,X4,X5) != X1
            & sK3(X0,X1,X2,X3,X4,X5) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) )
        & ( sK3(X0,X1,X2,X3,X4,X5) = X4
          | sK3(X0,X1,X2,X3,X4,X5) = X3
          | sK3(X0,X1,X2,X3,X4,X5) = X2
          | sK3(X0,X1,X2,X3,X4,X5) = X1
          | sK3(X0,X1,X2,X3,X4,X5) = X0
          | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5) ) ) ) ),
    introduced(choice_axiom,[])).

% (23716)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (23735)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (23734)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (23726)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (23725)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (23738)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (23717)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (23718)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% (23726)Refutation not found, incomplete strategy% (23726)------------------------------
% (23726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23737)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (23726)Termination reason: Refutation not found, incomplete strategy
% (23731)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (23733)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark

% (23726)Memory used [KB]: 10618
% (23726)Time elapsed: 0.142 s
% (23726)------------------------------
% (23726)------------------------------
fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X5)
              | ( X4 != X7
                & X3 != X7
                & X2 != X7
                & X1 != X7
                & X0 != X7 ) )
            & ( X4 = X7
              | X3 = X7
              | X2 = X7
              | X1 = X7
              | X0 = X7
              | ~ r2_hidden(X7,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( k3_enumset1(X0,X1,X2,X3,X4) = X5
        | ? [X6] :
            ( ( ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 )
              | ~ r2_hidden(X6,X5) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | r2_hidden(X6,X5) ) ) )
      & ( ! [X6] :
            ( ( r2_hidden(X6,X5)
              | ( X4 != X6
                & X3 != X6
                & X2 != X6
                & X1 != X6
                & X0 != X6 ) )
            & ( X4 = X6
              | X3 = X6
              | X2 = X6
              | X1 = X6
              | X0 = X6
              | ~ r2_hidden(X6,X5) ) )
        | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ( X4 = X6
            | X3 = X6
            | X2 = X6
            | X1 = X6
            | X0 = X6 ) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k3_enumset1(X0,X1,X2,X3,X4) = X5
    <=> ! [X6] :
          ( r2_hidden(X6,X5)
        <=> ~ ( X4 != X6
              & X3 != X6
              & X2 != X6
              & X1 != X6
              & X0 != X6 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).

fof(f206,plain,
    ( r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f205])).

fof(f193,plain,
    ( spl4_1
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f183,f96])).

fof(f96,plain,(
    ! [X2,X0,X7,X3,X1] : r2_hidden(X7,k3_enumset1(X0,X1,X2,X3,X7)) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | k3_enumset1(X0,X1,X2,X3,X7) != X5 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X7,X5,X3,X1] :
      ( r2_hidden(X7,X5)
      | X4 != X7
      | k3_enumset1(X0,X1,X2,X3,X4) != X5 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f183,plain,
    ( ~ r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))
    | spl4_1
    | ~ spl4_7 ),
    inference(resolution,[],[f177,f92])).

fof(f92,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f177,plain,
    ( ~ r2_hidden(sK0,k2_xboole_0(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)))
    | spl4_1
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f108,f139])).

fof(f139,plain,
    ( sK0 = sK1
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f138])).

fof(f151,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f150])).

fof(f150,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f49,f149])).

fof(f149,plain,
    ( ~ v3_ordinal1(sK0)
    | spl4_8 ),
    inference(resolution,[],[f144,f57])).

fof(f57,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v1_ordinal1(X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f144,plain,
    ( ~ v1_ordinal1(sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl4_8
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f49,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ r1_ordinal1(sK0,sK1)
      | ~ r2_hidden(sK0,k1_ordinal1(sK1)) )
    & ( r1_ordinal1(sK0,sK1)
      | r2_hidden(sK0,k1_ordinal1(sK1)) )
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).

fof(f35,plain,
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

fof(f36,plain,
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

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r1_ordinal1(X0,X1)
            | ~ r2_hidden(X0,k1_ordinal1(X1)) )
          & ( r1_ordinal1(X0,X1)
            | r2_hidden(X0,k1_ordinal1(X1)) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <~> r1_ordinal1(X0,X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,k1_ordinal1(X1))
            <=> r1_ordinal1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f148,plain,
    ( ~ spl4_8
    | ~ spl4_4
    | spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f141,f135,f146,f121,f143])).

fof(f141,plain,
    ( r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v1_ordinal1(sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f136,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f136,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f135])).

fof(f132,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl4_4 ),
    inference(subsumption_resolution,[],[f50,f122])).

fof(f122,plain,
    ( ~ v3_ordinal1(sK1)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f121])).

fof(f50,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f37])).

fof(f130,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f49,f119])).

fof(f119,plain,
    ( ~ v3_ordinal1(sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f115,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f90,f110,f107])).

fof(f90,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k2_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f51,f88])).

fof(f88,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k3_enumset1(X0,X0,X0,X0,X0)) ),
    inference(definition_unfolding,[],[f55,f87])).

fof(f87,plain,(
    ! [X0] : k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f54,f86])).

fof(f86,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f59,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f65,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f65,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f59,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f55,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f51,plain,
    ( r1_ordinal1(sK0,sK1)
    | r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f112,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f89,f110,f107])).

fof(f89,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k2_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) ),
    inference(definition_unfolding,[],[f52,f88])).

fof(f52,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | ~ r2_hidden(sK0,k1_ordinal1(sK1)) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:11:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (23729)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.50  % (23730)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.51  % (23722)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.51  % (23712)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.51  % (23714)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (23719)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.52  % (23721)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (23719)Refutation not found, incomplete strategy% (23719)------------------------------
% 0.22/0.52  % (23719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23719)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (23719)Memory used [KB]: 10746
% 0.22/0.52  % (23719)Time elapsed: 0.111 s
% 0.22/0.52  % (23719)------------------------------
% 0.22/0.52  % (23719)------------------------------
% 0.22/0.52  % (23732)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (23720)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (23723)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (23715)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.53  % (23709)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (23736)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.53  % (23727)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.53  % (23724)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.53  % (23728)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (23710)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (23720)Refutation not found, incomplete strategy% (23720)------------------------------
% 0.22/0.54  % (23720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (23720)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (23720)Memory used [KB]: 10746
% 0.22/0.54  % (23720)Time elapsed: 0.117 s
% 0.22/0.54  % (23720)------------------------------
% 0.22/0.54  % (23720)------------------------------
% 0.22/0.54  % (23711)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (23713)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (23711)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f257,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f112,f115,f130,f132,f148,f151,f193,f226,f237,f239,f241,f245,f249,f252,f256])).
% 0.22/0.54  fof(f256,plain,(
% 0.22/0.54    ~spl4_11),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f255])).
% 0.22/0.54  fof(f255,plain,(
% 0.22/0.54    $false | ~spl4_11),
% 0.22/0.54    inference(subsumption_resolution,[],[f174,f253])).
% 0.22/0.54  fof(f253,plain,(
% 0.22/0.54    ~r2_hidden(sK0,sK0) | ~spl4_11),
% 0.22/0.54    inference(resolution,[],[f174,f60])).
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f26])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.22/0.54  fof(f174,plain,(
% 0.22/0.54    r2_hidden(sK0,sK0) | ~spl4_11),
% 0.22/0.54    inference(avatar_component_clause,[],[f173])).
% 0.22/0.54  fof(f173,plain,(
% 0.22/0.54    spl4_11 <=> r2_hidden(sK0,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.54  fof(f252,plain,(
% 0.22/0.54    spl4_13 | spl4_9 | ~spl4_1),
% 0.22/0.54    inference(avatar_split_clause,[],[f250,f107,f146,f205])).
% 0.22/0.54  fof(f205,plain,(
% 0.22/0.54    spl4_13 <=> r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.54  fof(f146,plain,(
% 0.22/0.54    spl4_9 <=> r2_hidden(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.54  fof(f107,plain,(
% 0.22/0.54    spl4_1 <=> r2_hidden(sK0,k2_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.54  fof(f250,plain,(
% 0.22/0.54    r2_hidden(sK0,sK1) | r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl4_1),
% 0.22/0.54    inference(resolution,[],[f113,f94])).
% 0.22/0.54  fof(f94,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_xboole_0(X0,X1)) | r2_hidden(X4,X0) | r2_hidden(X4,X1)) )),
% 0.22/0.54    inference(equality_resolution,[],[f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f43])).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK2(X0,X1,X2),X1) & ~r2_hidden(sK2(X0,X1,X2),X0)) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X0) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(rectify,[],[f40])).
% 0.22/0.54  fof(f40,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(flattening,[],[f39])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.22/0.54    inference(nnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.22/0.54  fof(f113,plain,(
% 0.22/0.54    r2_hidden(sK0,k2_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | ~spl4_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f107])).
% 0.22/0.54  fof(f249,plain,(
% 0.22/0.54    ~spl4_3 | ~spl4_4 | spl4_12 | spl4_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f247,f110,f199,f121,f118])).
% 0.22/0.54  fof(f118,plain,(
% 0.22/0.54    spl4_3 <=> v3_ordinal1(sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.54  fof(f121,plain,(
% 0.22/0.54    spl4_4 <=> v3_ordinal1(sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.54  fof(f199,plain,(
% 0.22/0.54    spl4_12 <=> r2_hidden(sK1,sK0)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.54  fof(f110,plain,(
% 0.22/0.54    spl4_2 <=> r1_ordinal1(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.54  fof(f247,plain,(
% 0.22/0.54    r2_hidden(sK1,sK0) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | spl4_2),
% 0.22/0.54    inference(resolution,[],[f111,f58])).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | r2_hidden(X1,X0) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,axiom,(
% 0.22/0.54    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) | r1_ordinal1(X0,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).
% 0.22/0.54  fof(f111,plain,(
% 0.22/0.54    ~r1_ordinal1(sK0,sK1) | spl4_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f110])).
% 0.22/0.54  fof(f245,plain,(
% 0.22/0.54    spl4_1 | ~spl4_9),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f244])).
% 0.22/0.54  fof(f244,plain,(
% 0.22/0.54    $false | (spl4_1 | ~spl4_9)),
% 0.22/0.54    inference(subsumption_resolution,[],[f147,f242])).
% 0.22/0.54  fof(f242,plain,(
% 0.22/0.54    ~r2_hidden(sK0,sK1) | spl4_1),
% 0.22/0.54    inference(resolution,[],[f108,f93])).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.22/0.54    inference(equality_resolution,[],[f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f43])).
% 0.22/0.54  fof(f108,plain,(
% 0.22/0.54    ~r2_hidden(sK0,k2_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1))) | spl4_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f107])).
% 0.22/0.54  fof(f147,plain,(
% 0.22/0.54    r2_hidden(sK0,sK1) | ~spl4_9),
% 0.22/0.54    inference(avatar_component_clause,[],[f146])).
% 0.22/0.54  fof(f241,plain,(
% 0.22/0.54    spl4_6 | spl4_7 | ~spl4_5),
% 0.22/0.54    inference(avatar_split_clause,[],[f240,f124,f138,f135])).
% 0.22/0.54  fof(f135,plain,(
% 0.22/0.54    spl4_6 <=> r2_xboole_0(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.54  fof(f138,plain,(
% 0.22/0.54    spl4_7 <=> sK0 = sK1),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.54  fof(f124,plain,(
% 0.22/0.54    spl4_5 <=> r1_tarski(sK0,sK1)),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.54  fof(f240,plain,(
% 0.22/0.54    sK0 = sK1 | r2_xboole_0(sK0,sK1) | ~spl4_5),
% 0.22/0.54    inference(resolution,[],[f125,f64])).
% 0.22/0.54  fof(f64,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f31])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.54    inference(flattening,[],[f30])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 0.22/0.54    inference(ennf_transformation,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 0.22/0.54    inference(unused_predicate_definition_removal,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.54  fof(f125,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1) | ~spl4_5),
% 0.22/0.54    inference(avatar_component_clause,[],[f124])).
% 0.22/0.54  fof(f239,plain,(
% 0.22/0.54    ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_2),
% 0.22/0.54    inference(avatar_split_clause,[],[f238,f110,f124,f121,f118])).
% 0.22/0.54  fof(f238,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~spl4_2),
% 0.22/0.54    inference(resolution,[],[f114,f62])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f38])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(nnf_transformation,[],[f29])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 0.22/0.54    inference(flattening,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,axiom,(
% 0.22/0.54    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 0.22/0.54  fof(f114,plain,(
% 0.22/0.54    r1_ordinal1(sK0,sK1) | ~spl4_2),
% 0.22/0.54    inference(avatar_component_clause,[],[f110])).
% 0.22/0.54  fof(f237,plain,(
% 0.22/0.54    ~spl4_9 | ~spl4_12),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f235])).
% 0.22/0.54  fof(f235,plain,(
% 0.22/0.54    $false | (~spl4_9 | ~spl4_12)),
% 0.22/0.54    inference(subsumption_resolution,[],[f209,f147])).
% 0.22/0.54  fof(f209,plain,(
% 0.22/0.54    ~r2_hidden(sK0,sK1) | ~spl4_12),
% 0.22/0.54    inference(resolution,[],[f200,f60])).
% 0.22/0.54  fof(f200,plain,(
% 0.22/0.54    r2_hidden(sK1,sK0) | ~spl4_12),
% 0.22/0.54    inference(avatar_component_clause,[],[f199])).
% 0.22/0.54  fof(f226,plain,(
% 0.22/0.54    ~spl4_3 | spl4_11 | spl4_2 | ~spl4_13),
% 0.22/0.54    inference(avatar_split_clause,[],[f223,f205,f110,f173,f118])).
% 0.22/0.54  fof(f223,plain,(
% 0.22/0.54    r2_hidden(sK0,sK0) | ~v3_ordinal1(sK0) | (spl4_2 | ~spl4_13)),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f222])).
% 0.22/0.54  fof(f222,plain,(
% 0.22/0.54    r2_hidden(sK0,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK0) | (spl4_2 | ~spl4_13)),
% 0.22/0.54    inference(resolution,[],[f214,f58])).
% 0.22/0.54  fof(f214,plain,(
% 0.22/0.54    ~r1_ordinal1(sK0,sK0) | (spl4_2 | ~spl4_13)),
% 0.22/0.54    inference(backward_demodulation,[],[f111,f212])).
% 0.22/0.54  fof(f212,plain,(
% 0.22/0.54    sK0 = sK1 | ~spl4_13),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f210])).
% 0.22/0.54  fof(f210,plain,(
% 0.22/0.54    sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | sK0 = sK1 | ~spl4_13),
% 0.22/0.54    inference(resolution,[],[f206,f105])).
% 0.22/0.54  fof(f105,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X7,X3,X1] : (~r2_hidden(X7,k3_enumset1(X0,X1,X2,X3,X4)) | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | X4 = X7) )),
% 0.22/0.54    inference(equality_resolution,[],[f73])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X7,X5,X3,X1] : (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5) | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 0.22/0.54    inference(cnf_transformation,[],[f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | (((sK3(X0,X1,X2,X3,X4,X5) != X4 & sK3(X0,X1,X2,X3,X4,X5) != X3 & sK3(X0,X1,X2,X3,X4,X5) != X2 & sK3(X0,X1,X2,X3,X4,X5) != X1 & sK3(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)) & (sK3(X0,X1,X2,X3,X4,X5) = X4 | sK3(X0,X1,X2,X3,X4,X5) = X3 | sK3(X0,X1,X2,X3,X4,X5) = X2 | sK3(X0,X1,X2,X3,X4,X5) = X1 | sK3(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).
% 0.22/0.54  fof(f47,plain,(
% 0.22/0.54    ! [X5,X4,X3,X2,X1,X0] : (? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5))) => (((sK3(X0,X1,X2,X3,X4,X5) != X4 & sK3(X0,X1,X2,X3,X4,X5) != X3 & sK3(X0,X1,X2,X3,X4,X5) != X2 & sK3(X0,X1,X2,X3,X4,X5) != X1 & sK3(X0,X1,X2,X3,X4,X5) != X0) | ~r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5)) & (sK3(X0,X1,X2,X3,X4,X5) = X4 | sK3(X0,X1,X2,X3,X4,X5) = X3 | sK3(X0,X1,X2,X3,X4,X5) = X2 | sK3(X0,X1,X2,X3,X4,X5) = X1 | sK3(X0,X1,X2,X3,X4,X5) = X0 | r2_hidden(sK3(X0,X1,X2,X3,X4,X5),X5))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  % (23716)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (23735)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.54  % (23734)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.54  % (23726)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (23725)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.55  % (23738)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.55  % (23717)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (23718)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.55  % (23726)Refutation not found, incomplete strategy% (23726)------------------------------
% 0.22/0.55  % (23726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (23737)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (23726)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  % (23731)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.56  % (23733)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.56  
% 0.22/0.56  % (23726)Memory used [KB]: 10618
% 0.22/0.56  % (23726)Time elapsed: 0.142 s
% 0.22/0.56  % (23726)------------------------------
% 0.22/0.56  % (23726)------------------------------
% 0.22/0.56  fof(f46,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X7] : ((r2_hidden(X7,X5) | (X4 != X7 & X3 != X7 & X2 != X7 & X1 != X7 & X0 != X7)) & (X4 = X7 | X3 = X7 | X2 = X7 | X1 = X7 | X0 = X7 | ~r2_hidden(X7,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.22/0.56    inference(rectify,[],[f45])).
% 0.22/0.56  fof(f45,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6 | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.22/0.56    inference(flattening,[],[f44])).
% 0.22/0.56  fof(f44,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((k3_enumset1(X0,X1,X2,X3,X4) = X5 | ? [X6] : (((X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6) | ~r2_hidden(X6,X5)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | r2_hidden(X6,X5)))) & (! [X6] : ((r2_hidden(X6,X5) | (X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)) & ((X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6) | ~r2_hidden(X6,X5))) | k3_enumset1(X0,X1,X2,X3,X4) != X5))),
% 0.22/0.56    inference(nnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> (X4 = X6 | X3 = X6 | X2 = X6 | X1 = X6 | X0 = X6)))),
% 0.22/0.56    inference(ennf_transformation,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : (k3_enumset1(X0,X1,X2,X3,X4) = X5 <=> ! [X6] : (r2_hidden(X6,X5) <=> ~(X4 != X6 & X3 != X6 & X2 != X6 & X1 != X6 & X0 != X6)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_enumset1)).
% 0.22/0.56  fof(f206,plain,(
% 0.22/0.56    r2_hidden(sK0,k3_enumset1(sK1,sK1,sK1,sK1,sK1)) | ~spl4_13),
% 0.22/0.56    inference(avatar_component_clause,[],[f205])).
% 0.22/0.56  fof(f193,plain,(
% 0.22/0.56    spl4_1 | ~spl4_7),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f184])).
% 0.22/0.56  fof(f184,plain,(
% 0.22/0.56    $false | (spl4_1 | ~spl4_7)),
% 0.22/0.56    inference(resolution,[],[f183,f96])).
% 0.22/0.56  fof(f96,plain,(
% 0.22/0.56    ( ! [X2,X0,X7,X3,X1] : (r2_hidden(X7,k3_enumset1(X0,X1,X2,X3,X7))) )),
% 0.22/0.56    inference(equality_resolution,[],[f95])).
% 1.58/0.56  fof(f95,plain,(
% 1.58/0.56    ( ! [X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | k3_enumset1(X0,X1,X2,X3,X7) != X5) )),
% 1.58/0.56    inference(equality_resolution,[],[f78])).
% 1.58/0.56  fof(f78,plain,(
% 1.58/0.56    ( ! [X4,X2,X0,X7,X5,X3,X1] : (r2_hidden(X7,X5) | X4 != X7 | k3_enumset1(X0,X1,X2,X3,X4) != X5) )),
% 1.58/0.56    inference(cnf_transformation,[],[f48])).
% 1.58/0.56  fof(f183,plain,(
% 1.58/0.56    ~r2_hidden(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0)) | (spl4_1 | ~spl4_7)),
% 1.58/0.56    inference(resolution,[],[f177,f92])).
% 1.58/0.56  fof(f92,plain,(
% 1.58/0.56    ( ! [X4,X0,X1] : (r2_hidden(X4,k2_xboole_0(X0,X1)) | ~r2_hidden(X4,X1)) )),
% 1.58/0.56    inference(equality_resolution,[],[f68])).
% 1.58/0.56  fof(f68,plain,(
% 1.58/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 1.58/0.56    inference(cnf_transformation,[],[f43])).
% 1.58/0.56  fof(f177,plain,(
% 1.58/0.56    ~r2_hidden(sK0,k2_xboole_0(sK0,k3_enumset1(sK0,sK0,sK0,sK0,sK0))) | (spl4_1 | ~spl4_7)),
% 1.58/0.56    inference(forward_demodulation,[],[f108,f139])).
% 1.58/0.56  fof(f139,plain,(
% 1.58/0.56    sK0 = sK1 | ~spl4_7),
% 1.58/0.56    inference(avatar_component_clause,[],[f138])).
% 1.58/0.56  fof(f151,plain,(
% 1.58/0.56    spl4_8),
% 1.58/0.56    inference(avatar_contradiction_clause,[],[f150])).
% 1.58/0.56  fof(f150,plain,(
% 1.58/0.56    $false | spl4_8),
% 1.58/0.56    inference(subsumption_resolution,[],[f49,f149])).
% 1.58/0.56  fof(f149,plain,(
% 1.58/0.56    ~v3_ordinal1(sK0) | spl4_8),
% 1.58/0.56    inference(resolution,[],[f144,f57])).
% 1.58/0.56  fof(f57,plain,(
% 1.58/0.56    ( ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 1.58/0.56    inference(cnf_transformation,[],[f23])).
% 1.58/0.56  fof(f23,plain,(
% 1.58/0.56    ! [X0] : (v1_ordinal1(X0) | ~v3_ordinal1(X0))),
% 1.58/0.56    inference(ennf_transformation,[],[f19])).
% 1.58/0.56  fof(f19,plain,(
% 1.58/0.56    ! [X0] : (v3_ordinal1(X0) => v1_ordinal1(X0))),
% 1.58/0.56    inference(pure_predicate_removal,[],[f11])).
% 1.58/0.56  fof(f11,axiom,(
% 1.58/0.56    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 1.58/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 1.58/0.56  fof(f144,plain,(
% 1.58/0.56    ~v1_ordinal1(sK0) | spl4_8),
% 1.58/0.56    inference(avatar_component_clause,[],[f143])).
% 1.58/0.56  fof(f143,plain,(
% 1.58/0.56    spl4_8 <=> v1_ordinal1(sK0)),
% 1.58/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.58/0.56  fof(f49,plain,(
% 1.58/0.56    v3_ordinal1(sK0)),
% 1.58/0.56    inference(cnf_transformation,[],[f37])).
% 1.58/0.56  fof(f37,plain,(
% 1.58/0.56    ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 1.58/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f36,f35])).
% 1.58/0.56  fof(f35,plain,(
% 1.58/0.56    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 1.58/0.56    introduced(choice_axiom,[])).
% 1.58/0.56  fof(f36,plain,(
% 1.58/0.56    ? [X1] : ((~r1_ordinal1(sK0,X1) | ~r2_hidden(sK0,k1_ordinal1(X1))) & (r1_ordinal1(sK0,X1) | r2_hidden(sK0,k1_ordinal1(X1))) & v3_ordinal1(X1)) => ((~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))) & (r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))) & v3_ordinal1(sK1))),
% 1.58/0.56    introduced(choice_axiom,[])).
% 1.58/0.56  fof(f34,plain,(
% 1.58/0.56    ? [X0] : (? [X1] : ((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.58/0.56    inference(flattening,[],[f33])).
% 1.58/0.56  fof(f33,plain,(
% 1.58/0.56    ? [X0] : (? [X1] : (((~r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) & (r1_ordinal1(X0,X1) | r2_hidden(X0,k1_ordinal1(X1)))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.58/0.56    inference(nnf_transformation,[],[f20])).
% 1.58/0.56  fof(f20,plain,(
% 1.58/0.56    ? [X0] : (? [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <~> r1_ordinal1(X0,X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.58/0.56    inference(ennf_transformation,[],[f17])).
% 1.58/0.56  fof(f17,negated_conjecture,(
% 1.58/0.56    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.58/0.56    inference(negated_conjecture,[],[f16])).
% 1.58/0.56  fof(f16,conjecture,(
% 1.58/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.58/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.58/0.56  fof(f148,plain,(
% 1.58/0.56    ~spl4_8 | ~spl4_4 | spl4_9 | ~spl4_6),
% 1.58/0.56    inference(avatar_split_clause,[],[f141,f135,f146,f121,f143])).
% 1.58/0.56  fof(f141,plain,(
% 1.58/0.56    r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v1_ordinal1(sK0) | ~spl4_6),
% 1.58/0.56    inference(resolution,[],[f136,f56])).
% 1.58/0.56  fof(f56,plain,(
% 1.58/0.56    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v1_ordinal1(X0)) )),
% 1.58/0.56    inference(cnf_transformation,[],[f22])).
% 1.58/0.56  fof(f22,plain,(
% 1.58/0.56    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.58/0.56    inference(flattening,[],[f21])).
% 1.58/0.56  fof(f21,plain,(
% 1.58/0.56    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.58/0.56    inference(ennf_transformation,[],[f14])).
% 1.58/0.56  fof(f14,axiom,(
% 1.58/0.56    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 1.58/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).
% 1.58/0.56  fof(f136,plain,(
% 1.58/0.56    r2_xboole_0(sK0,sK1) | ~spl4_6),
% 1.58/0.56    inference(avatar_component_clause,[],[f135])).
% 1.58/0.56  fof(f132,plain,(
% 1.58/0.56    spl4_4),
% 1.58/0.56    inference(avatar_contradiction_clause,[],[f131])).
% 1.58/0.56  fof(f131,plain,(
% 1.58/0.56    $false | spl4_4),
% 1.58/0.56    inference(subsumption_resolution,[],[f50,f122])).
% 1.58/0.56  fof(f122,plain,(
% 1.58/0.56    ~v3_ordinal1(sK1) | spl4_4),
% 1.58/0.56    inference(avatar_component_clause,[],[f121])).
% 1.58/0.56  fof(f50,plain,(
% 1.58/0.56    v3_ordinal1(sK1)),
% 1.58/0.56    inference(cnf_transformation,[],[f37])).
% 1.58/0.56  fof(f130,plain,(
% 1.58/0.56    spl4_3),
% 1.58/0.56    inference(avatar_contradiction_clause,[],[f129])).
% 1.58/0.56  fof(f129,plain,(
% 1.58/0.56    $false | spl4_3),
% 1.58/0.56    inference(subsumption_resolution,[],[f49,f119])).
% 1.58/0.56  fof(f119,plain,(
% 1.58/0.56    ~v3_ordinal1(sK0) | spl4_3),
% 1.58/0.56    inference(avatar_component_clause,[],[f118])).
% 1.58/0.56  fof(f115,plain,(
% 1.58/0.56    spl4_1 | spl4_2),
% 1.58/0.56    inference(avatar_split_clause,[],[f90,f110,f107])).
% 1.58/0.56  fof(f90,plain,(
% 1.58/0.56    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k2_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.58/0.56    inference(definition_unfolding,[],[f51,f88])).
% 1.58/0.56  fof(f88,plain,(
% 1.58/0.56    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k3_enumset1(X0,X0,X0,X0,X0))) )),
% 1.58/0.56    inference(definition_unfolding,[],[f55,f87])).
% 1.58/0.56  fof(f87,plain,(
% 1.58/0.56    ( ! [X0] : (k1_tarski(X0) = k3_enumset1(X0,X0,X0,X0,X0)) )),
% 1.58/0.56    inference(definition_unfolding,[],[f54,f86])).
% 1.58/0.56  fof(f86,plain,(
% 1.58/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_enumset1(X0,X0,X0,X0,X1)) )),
% 1.58/0.56    inference(definition_unfolding,[],[f59,f85])).
% 1.58/0.56  fof(f85,plain,(
% 1.58/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_enumset1(X0,X0,X0,X1,X2)) )),
% 1.58/0.56    inference(definition_unfolding,[],[f65,f72])).
% 1.58/0.56  fof(f72,plain,(
% 1.58/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.58/0.56    inference(cnf_transformation,[],[f7])).
% 1.58/0.56  fof(f7,axiom,(
% 1.58/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.58/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.58/0.56  fof(f65,plain,(
% 1.58/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.58/0.56    inference(cnf_transformation,[],[f6])).
% 1.58/0.56  fof(f6,axiom,(
% 1.58/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.58/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.58/0.56  fof(f59,plain,(
% 1.58/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.58/0.56    inference(cnf_transformation,[],[f5])).
% 1.58/0.56  fof(f5,axiom,(
% 1.58/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.58/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.58/0.56  fof(f54,plain,(
% 1.58/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.58/0.56    inference(cnf_transformation,[],[f4])).
% 1.58/0.56  fof(f4,axiom,(
% 1.58/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.58/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.58/0.56  fof(f55,plain,(
% 1.58/0.56    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.58/0.56    inference(cnf_transformation,[],[f12])).
% 1.58/0.56  fof(f12,axiom,(
% 1.58/0.56    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.58/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.58/0.56  fof(f51,plain,(
% 1.58/0.56    r1_ordinal1(sK0,sK1) | r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.58/0.56    inference(cnf_transformation,[],[f37])).
% 1.58/0.56  fof(f112,plain,(
% 1.58/0.56    ~spl4_1 | ~spl4_2),
% 1.58/0.56    inference(avatar_split_clause,[],[f89,f110,f107])).
% 1.58/0.56  fof(f89,plain,(
% 1.58/0.56    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k2_xboole_0(sK1,k3_enumset1(sK1,sK1,sK1,sK1,sK1)))),
% 1.58/0.56    inference(definition_unfolding,[],[f52,f88])).
% 1.58/0.56  fof(f52,plain,(
% 1.58/0.56    ~r1_ordinal1(sK0,sK1) | ~r2_hidden(sK0,k1_ordinal1(sK1))),
% 1.58/0.56    inference(cnf_transformation,[],[f37])).
% 1.58/0.56  % SZS output end Proof for theBenchmark
% 1.58/0.56  % (23711)------------------------------
% 1.58/0.56  % (23711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.56  % (23711)Termination reason: Refutation
% 1.58/0.56  
% 1.58/0.56  % (23711)Memory used [KB]: 10746
% 1.58/0.56  % (23711)Time elapsed: 0.130 s
% 1.58/0.56  % (23711)------------------------------
% 1.58/0.56  % (23711)------------------------------
% 1.58/0.57  % (23707)Success in time 0.202 s
%------------------------------------------------------------------------------

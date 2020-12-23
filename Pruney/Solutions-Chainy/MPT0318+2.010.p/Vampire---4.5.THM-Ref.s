%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:17 EST 2020

% Result     : Theorem 0.75s
% Output     : Refutation 0.75s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 191 expanded)
%              Number of leaves         :   21 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  295 ( 574 expanded)
%              Number of equality atoms :  160 ( 339 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f80,f93,f103,f106,f148,f157,f177])).

fof(f177,plain,
    ( ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f167,f143])).

fof(f143,plain,
    ( r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_5
  <=> r2_hidden(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f167,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | ~ spl4_6 ),
    inference(resolution,[],[f147,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f113,f32])).

fof(f32,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f113,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X1)) ) ),
    inference(factoring,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f147,plain,
    ( ! [X15] : ~ r2_hidden(sK2,k5_xboole_0(X15,k1_xboole_0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl4_6
  <=> ! [X15] : ~ r2_hidden(sK2,k5_xboole_0(X15,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f157,plain,
    ( ~ spl4_3
    | spl4_5 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | ~ spl4_3
    | spl4_5 ),
    inference(resolution,[],[f152,f129])).

fof(f129,plain,
    ( sP0(sK2,sK2,sK2,k1_xboole_0)
    | ~ spl4_3 ),
    inference(superposition,[],[f71,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_3
  <=> k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f71,plain,(
    ! [X2,X0,X1] : sP0(X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f52,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f38,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f58])).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f54,f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f56,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f54,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f38,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP0(X2,X1,X0,X3) )
      & ( sP0(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP0(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f16,f17])).

fof(f17,plain,(
    ! [X2,X1,X0,X3] :
      ( sP0(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f152,plain,
    ( ! [X4,X3] : ~ sP0(sK2,X3,X4,k1_xboole_0)
    | spl4_5 ),
    inference(resolution,[],[f144,f68])).

fof(f68,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | ~ sP0(X5,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ( sK3(X0,X1,X2,X3) != X0
              & sK3(X0,X1,X2,X3) != X1
              & sK3(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
          & ( sK3(X0,X1,X2,X3) = X0
            | sK3(X0,X1,X2,X3) = X1
            | sK3(X0,X1,X2,X3) = X2
            | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK3(X0,X1,X2,X3) != X0
            & sK3(X0,X1,X2,X3) != X1
            & sK3(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK3(X0,X1,X2,X3),X3) )
        & ( sK3(X0,X1,X2,X3) = X0
          | sK3(X0,X1,X2,X3) = X1
          | sK3(X0,X1,X2,X3) = X2
          | r2_hidden(sK3(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f25])).

fof(f25,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP0(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f144,plain,
    ( ~ r2_hidden(sK2,k1_xboole_0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f142])).

fof(f148,plain,
    ( ~ spl4_5
    | spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f140,f86,f146,f142])).

fof(f140,plain,
    ( ! [X15] :
        ( ~ r2_hidden(sK2,k5_xboole_0(X15,k1_xboole_0))
        | ~ r2_hidden(sK2,k1_xboole_0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f131,f114])).

fof(f131,plain,
    ( ! [X4] :
        ( ~ r2_hidden(sK2,X4)
        | ~ r2_hidden(sK2,k5_xboole_0(X4,k1_xboole_0)) )
    | ~ spl4_3 ),
    inference(resolution,[],[f116,f129])).

fof(f116,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ sP0(X7,X8,X4,X6)
      | ~ r2_hidden(X4,k5_xboole_0(X5,X6))
      | ~ r2_hidden(X4,X5) ) ),
    inference(resolution,[],[f40,f70])).

fof(f70,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | ~ sP0(X0,X1,X5,X3) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f106,plain,
    ( spl4_4
    | spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f105,f73,f86,f90])).

fof(f90,plain,
    ( spl4_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f73,plain,
    ( spl4_1
  <=> k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f105,plain,
    ( k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = sK1
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 = sK1
    | ~ spl4_1 ),
    inference(superposition,[],[f35,f75])).

fof(f75,plain,
    ( k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f103,plain,(
    ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f101])).

fof(f101,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl4_4 ),
    inference(superposition,[],[f30,f92])).

fof(f92,plain,
    ( k1_xboole_0 = sK1
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f30,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ( k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2))
      | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1) )
    & k1_xboole_0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f19])).

fof(f19,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
          | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
        & k1_xboole_0 != X0 )
   => ( ( k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1) )
      & k1_xboole_0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1))
        | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0) )
      & k1_xboole_0 != X0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 != X0
       => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
          & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
     => ( k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1))
        & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

fof(f93,plain,
    ( spl4_3
    | spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f84,f77,f90,f86])).

fof(f77,plain,
    ( spl4_2
  <=> k1_xboole_0 = k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f84,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f83])).

fof(f83,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK1
    | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl4_2 ),
    inference(superposition,[],[f35,f79])).

fof(f79,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f77])).

fof(f80,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f63,f77,f73])).

fof(f63,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))
    | k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1) ),
    inference(definition_unfolding,[],[f31,f62,f62])).

fof(f62,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f33,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f34,f60])).

fof(f34,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f31,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2))
    | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:56:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.36  ipcrm: permission denied for id (808091649)
% 0.14/0.36  ipcrm: permission denied for id (808124418)
% 0.14/0.36  ipcrm: permission denied for id (808157189)
% 0.14/0.36  ipcrm: permission denied for id (808189958)
% 0.14/0.36  ipcrm: permission denied for id (808222727)
% 0.14/0.37  ipcrm: permission denied for id (808255498)
% 0.14/0.38  ipcrm: permission denied for id (808353810)
% 0.14/0.38  ipcrm: permission denied for id (808386579)
% 0.21/0.38  ipcrm: permission denied for id (808452118)
% 0.21/0.39  ipcrm: permission denied for id (808550426)
% 0.21/0.39  ipcrm: permission denied for id (808583195)
% 0.21/0.39  ipcrm: permission denied for id (808615965)
% 0.21/0.39  ipcrm: permission denied for id (808681505)
% 0.21/0.40  ipcrm: permission denied for id (808812583)
% 0.21/0.40  ipcrm: permission denied for id (808878121)
% 0.21/0.41  ipcrm: permission denied for id (808943660)
% 0.21/0.41  ipcrm: permission denied for id (808976430)
% 0.21/0.41  ipcrm: permission denied for id (809041969)
% 0.21/0.42  ipcrm: permission denied for id (809271354)
% 0.21/0.43  ipcrm: permission denied for id (809304126)
% 0.21/0.43  ipcrm: permission denied for id (809369664)
% 0.21/0.43  ipcrm: permission denied for id (809402435)
% 0.21/0.44  ipcrm: permission denied for id (809435205)
% 0.21/0.44  ipcrm: permission denied for id (809599052)
% 0.21/0.45  ipcrm: permission denied for id (809631821)
% 0.21/0.45  ipcrm: permission denied for id (809664590)
% 0.21/0.45  ipcrm: permission denied for id (809697359)
% 0.21/0.45  ipcrm: permission denied for id (809730128)
% 0.21/0.45  ipcrm: permission denied for id (809762897)
% 0.21/0.45  ipcrm: permission denied for id (809861204)
% 0.21/0.46  ipcrm: permission denied for id (809992280)
% 0.21/0.47  ipcrm: permission denied for id (810057823)
% 0.21/0.48  ipcrm: permission denied for id (810156138)
% 0.21/0.48  ipcrm: permission denied for id (810188910)
% 0.21/0.49  ipcrm: permission denied for id (810319986)
% 0.21/0.49  ipcrm: permission denied for id (810385524)
% 0.21/0.50  ipcrm: permission denied for id (810451064)
% 0.21/0.50  ipcrm: permission denied for id (810483833)
% 0.21/0.50  ipcrm: permission denied for id (810516603)
% 0.75/0.63  % (15604)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.75/0.63  % (15612)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.75/0.64  % (15612)Refutation found. Thanks to Tanya!
% 0.75/0.64  % SZS status Theorem for theBenchmark
% 0.75/0.64  % (15628)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.75/0.65  % (15609)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.75/0.65  % (15619)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.75/0.66  % SZS output start Proof for theBenchmark
% 0.75/0.66  fof(f178,plain,(
% 0.75/0.66    $false),
% 0.75/0.66    inference(avatar_sat_refutation,[],[f80,f93,f103,f106,f148,f157,f177])).
% 0.75/0.66  fof(f177,plain,(
% 0.75/0.66    ~spl4_5 | ~spl4_6),
% 0.75/0.66    inference(avatar_contradiction_clause,[],[f169])).
% 0.75/0.66  fof(f169,plain,(
% 0.75/0.66    $false | (~spl4_5 | ~spl4_6)),
% 0.75/0.66    inference(resolution,[],[f167,f143])).
% 0.75/0.66  fof(f143,plain,(
% 0.75/0.66    r2_hidden(sK2,k1_xboole_0) | ~spl4_5),
% 0.75/0.66    inference(avatar_component_clause,[],[f142])).
% 0.75/0.66  fof(f142,plain,(
% 0.75/0.66    spl4_5 <=> r2_hidden(sK2,k1_xboole_0)),
% 0.75/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.75/0.66  fof(f167,plain,(
% 0.75/0.66    ~r2_hidden(sK2,k1_xboole_0) | ~spl4_6),
% 0.75/0.66    inference(resolution,[],[f147,f114])).
% 0.75/0.66  fof(f114,plain,(
% 0.75/0.66    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k1_xboole_0)) )),
% 0.75/0.66    inference(forward_demodulation,[],[f113,f32])).
% 0.75/0.66  fof(f32,plain,(
% 0.75/0.66    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.75/0.66    inference(cnf_transformation,[],[f2])).
% 0.75/0.66  fof(f2,axiom,(
% 0.75/0.66    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.75/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.75/0.66  fof(f113,plain,(
% 0.75/0.66    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X1))) )),
% 0.75/0.66    inference(factoring,[],[f39])).
% 0.75/0.66  fof(f39,plain,(
% 0.75/0.66    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.75/0.66    inference(cnf_transformation,[],[f23])).
% 0.75/0.66  fof(f23,plain,(
% 0.75/0.66    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.75/0.66    inference(nnf_transformation,[],[f15])).
% 0.75/0.66  fof(f15,plain,(
% 0.75/0.66    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.75/0.66    inference(ennf_transformation,[],[f1])).
% 0.75/0.66  fof(f1,axiom,(
% 0.75/0.66    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.75/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.75/0.66  fof(f147,plain,(
% 0.75/0.66    ( ! [X15] : (~r2_hidden(sK2,k5_xboole_0(X15,k1_xboole_0))) ) | ~spl4_6),
% 0.75/0.66    inference(avatar_component_clause,[],[f146])).
% 0.75/0.66  fof(f146,plain,(
% 0.75/0.66    spl4_6 <=> ! [X15] : ~r2_hidden(sK2,k5_xboole_0(X15,k1_xboole_0))),
% 0.75/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.75/0.66  fof(f157,plain,(
% 0.75/0.66    ~spl4_3 | spl4_5),
% 0.75/0.66    inference(avatar_contradiction_clause,[],[f156])).
% 0.75/0.66  fof(f156,plain,(
% 0.75/0.66    $false | (~spl4_3 | spl4_5)),
% 0.75/0.66    inference(resolution,[],[f152,f129])).
% 0.75/0.66  fof(f129,plain,(
% 0.75/0.66    sP0(sK2,sK2,sK2,k1_xboole_0) | ~spl4_3),
% 0.75/0.66    inference(superposition,[],[f71,f88])).
% 0.75/0.66  fof(f88,plain,(
% 0.75/0.66    k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl4_3),
% 0.75/0.66    inference(avatar_component_clause,[],[f86])).
% 0.75/0.66  fof(f86,plain,(
% 0.75/0.66    spl4_3 <=> k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 0.75/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.75/0.66  fof(f71,plain,(
% 0.75/0.66    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 0.75/0.66    inference(equality_resolution,[],[f65])).
% 0.75/0.66  fof(f65,plain,(
% 0.75/0.66    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 0.75/0.66    inference(definition_unfolding,[],[f52,f60])).
% 0.75/0.66  fof(f60,plain,(
% 0.75/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.75/0.66    inference(definition_unfolding,[],[f38,f59])).
% 0.75/0.66  fof(f59,plain,(
% 0.75/0.66    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.75/0.66    inference(definition_unfolding,[],[f43,f58])).
% 0.75/0.66  fof(f58,plain,(
% 0.75/0.66    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.75/0.66    inference(definition_unfolding,[],[f54,f57])).
% 0.75/0.66  fof(f57,plain,(
% 0.75/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.75/0.66    inference(definition_unfolding,[],[f55,f56])).
% 0.75/0.66  fof(f56,plain,(
% 0.75/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.75/0.66    inference(cnf_transformation,[],[f10])).
% 0.75/0.66  fof(f10,axiom,(
% 0.75/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.75/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.75/0.66  fof(f55,plain,(
% 0.75/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.75/0.66    inference(cnf_transformation,[],[f9])).
% 0.75/0.66  fof(f9,axiom,(
% 0.75/0.66    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.75/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.75/0.66  fof(f54,plain,(
% 0.75/0.66    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.75/0.66    inference(cnf_transformation,[],[f8])).
% 0.75/0.66  fof(f8,axiom,(
% 0.75/0.66    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.75/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.75/0.66  fof(f43,plain,(
% 0.75/0.66    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.75/0.66    inference(cnf_transformation,[],[f7])).
% 0.75/0.66  fof(f7,axiom,(
% 0.75/0.66    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.75/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.75/0.66  fof(f38,plain,(
% 0.75/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 0.75/0.66    inference(cnf_transformation,[],[f6])).
% 0.75/0.66  fof(f6,axiom,(
% 0.75/0.66    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 0.75/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.75/0.66  fof(f52,plain,(
% 0.75/0.66    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 0.75/0.66    inference(cnf_transformation,[],[f29])).
% 0.75/0.66  fof(f29,plain,(
% 0.75/0.66    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 0.75/0.66    inference(nnf_transformation,[],[f18])).
% 0.75/0.66  fof(f18,plain,(
% 0.75/0.66    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP0(X2,X1,X0,X3))),
% 0.75/0.66    inference(definition_folding,[],[f16,f17])).
% 0.75/0.66  fof(f17,plain,(
% 0.75/0.66    ! [X2,X1,X0,X3] : (sP0(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.75/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.75/0.66  fof(f16,plain,(
% 0.75/0.66    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 0.75/0.66    inference(ennf_transformation,[],[f3])).
% 0.75/0.66  fof(f3,axiom,(
% 0.75/0.66    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 0.75/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 0.75/0.66  fof(f152,plain,(
% 0.75/0.66    ( ! [X4,X3] : (~sP0(sK2,X3,X4,k1_xboole_0)) ) | spl4_5),
% 0.75/0.66    inference(resolution,[],[f144,f68])).
% 0.75/0.66  fof(f68,plain,(
% 0.75/0.66    ( ! [X2,X5,X3,X1] : (r2_hidden(X5,X3) | ~sP0(X5,X1,X2,X3)) )),
% 0.75/0.66    inference(equality_resolution,[],[f47])).
% 0.75/0.66  fof(f47,plain,(
% 0.75/0.66    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X0 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 0.75/0.66    inference(cnf_transformation,[],[f28])).
% 0.75/0.66  fof(f28,plain,(
% 0.75/0.66    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (((sK3(X0,X1,X2,X3) != X0 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X2) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X0 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X2 | r2_hidden(sK3(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.75/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f26,f27])).
% 0.75/0.66  fof(f27,plain,(
% 0.75/0.66    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK3(X0,X1,X2,X3) != X0 & sK3(X0,X1,X2,X3) != X1 & sK3(X0,X1,X2,X3) != X2) | ~r2_hidden(sK3(X0,X1,X2,X3),X3)) & (sK3(X0,X1,X2,X3) = X0 | sK3(X0,X1,X2,X3) = X1 | sK3(X0,X1,X2,X3) = X2 | r2_hidden(sK3(X0,X1,X2,X3),X3))))),
% 0.75/0.66    introduced(choice_axiom,[])).
% 0.75/0.66  fof(f26,plain,(
% 0.75/0.66    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP0(X0,X1,X2,X3)))),
% 0.75/0.66    inference(rectify,[],[f25])).
% 0.75/0.66  fof(f25,plain,(
% 0.75/0.66    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.75/0.66    inference(flattening,[],[f24])).
% 0.75/0.66  fof(f24,plain,(
% 0.75/0.66    ! [X2,X1,X0,X3] : ((sP0(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP0(X2,X1,X0,X3)))),
% 0.75/0.66    inference(nnf_transformation,[],[f17])).
% 0.75/0.66  fof(f144,plain,(
% 0.75/0.66    ~r2_hidden(sK2,k1_xboole_0) | spl4_5),
% 0.75/0.66    inference(avatar_component_clause,[],[f142])).
% 0.75/0.66  fof(f148,plain,(
% 0.75/0.66    ~spl4_5 | spl4_6 | ~spl4_3),
% 0.75/0.66    inference(avatar_split_clause,[],[f140,f86,f146,f142])).
% 0.75/0.66  fof(f140,plain,(
% 0.75/0.66    ( ! [X15] : (~r2_hidden(sK2,k5_xboole_0(X15,k1_xboole_0)) | ~r2_hidden(sK2,k1_xboole_0)) ) | ~spl4_3),
% 0.75/0.66    inference(resolution,[],[f131,f114])).
% 0.75/0.66  fof(f131,plain,(
% 0.75/0.66    ( ! [X4] : (~r2_hidden(sK2,X4) | ~r2_hidden(sK2,k5_xboole_0(X4,k1_xboole_0))) ) | ~spl4_3),
% 0.75/0.66    inference(resolution,[],[f116,f129])).
% 0.75/0.66  fof(f116,plain,(
% 0.75/0.66    ( ! [X6,X4,X8,X7,X5] : (~sP0(X7,X8,X4,X6) | ~r2_hidden(X4,k5_xboole_0(X5,X6)) | ~r2_hidden(X4,X5)) )),
% 0.75/0.66    inference(resolution,[],[f40,f70])).
% 0.75/0.66  fof(f70,plain,(
% 0.75/0.66    ( ! [X0,X5,X3,X1] : (r2_hidden(X5,X3) | ~sP0(X0,X1,X5,X3)) )),
% 0.75/0.66    inference(equality_resolution,[],[f45])).
% 0.75/0.66  fof(f45,plain,(
% 0.75/0.66    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP0(X0,X1,X2,X3)) )),
% 0.75/0.66    inference(cnf_transformation,[],[f28])).
% 0.75/0.66  fof(f40,plain,(
% 0.75/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.75/0.66    inference(cnf_transformation,[],[f23])).
% 0.75/0.66  fof(f106,plain,(
% 0.75/0.66    spl4_4 | spl4_3 | ~spl4_1),
% 0.75/0.66    inference(avatar_split_clause,[],[f105,f73,f86,f90])).
% 0.75/0.66  fof(f90,plain,(
% 0.75/0.66    spl4_4 <=> k1_xboole_0 = sK1),
% 0.75/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.75/0.66  fof(f73,plain,(
% 0.75/0.66    spl4_1 <=> k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1)),
% 0.75/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.75/0.66  fof(f105,plain,(
% 0.75/0.66    k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = sK1 | ~spl4_1),
% 0.75/0.66    inference(trivial_inequality_removal,[],[f104])).
% 0.75/0.66  fof(f104,plain,(
% 0.75/0.66    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 = sK1 | ~spl4_1),
% 0.75/0.66    inference(superposition,[],[f35,f75])).
% 0.75/0.66  fof(f75,plain,(
% 0.75/0.66    k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1) | ~spl4_1),
% 0.75/0.66    inference(avatar_component_clause,[],[f73])).
% 0.75/0.66  fof(f35,plain,(
% 0.75/0.66    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 0.75/0.66    inference(cnf_transformation,[],[f22])).
% 0.75/0.66  fof(f22,plain,(
% 0.75/0.66    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.75/0.66    inference(flattening,[],[f21])).
% 0.75/0.66  fof(f21,plain,(
% 0.75/0.66    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.75/0.66    inference(nnf_transformation,[],[f11])).
% 0.75/0.66  fof(f11,axiom,(
% 0.75/0.66    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.75/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.75/0.66  fof(f103,plain,(
% 0.75/0.66    ~spl4_4),
% 0.75/0.66    inference(avatar_contradiction_clause,[],[f102])).
% 0.75/0.66  fof(f102,plain,(
% 0.75/0.66    $false | ~spl4_4),
% 0.75/0.66    inference(trivial_inequality_removal,[],[f101])).
% 0.75/0.66  fof(f101,plain,(
% 0.75/0.66    k1_xboole_0 != k1_xboole_0 | ~spl4_4),
% 0.75/0.66    inference(superposition,[],[f30,f92])).
% 0.75/0.66  fof(f92,plain,(
% 0.75/0.66    k1_xboole_0 = sK1 | ~spl4_4),
% 0.75/0.66    inference(avatar_component_clause,[],[f90])).
% 0.75/0.66  fof(f30,plain,(
% 0.75/0.66    k1_xboole_0 != sK1),
% 0.75/0.66    inference(cnf_transformation,[],[f20])).
% 0.75/0.66  fof(f20,plain,(
% 0.75/0.66    (k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1)) & k1_xboole_0 != sK1),
% 0.75/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f19])).
% 0.75/0.66  fof(f19,plain,(
% 0.75/0.66    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0) => ((k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1)) & k1_xboole_0 != sK1)),
% 0.75/0.66    introduced(choice_axiom,[])).
% 0.75/0.66  fof(f14,plain,(
% 0.75/0.66    ? [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,k1_tarski(X1)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(X1),X0)) & k1_xboole_0 != X0)),
% 0.75/0.66    inference(ennf_transformation,[],[f13])).
% 0.75/0.66  fof(f13,negated_conjecture,(
% 0.75/0.66    ~! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.75/0.66    inference(negated_conjecture,[],[f12])).
% 0.75/0.66  fof(f12,conjecture,(
% 0.75/0.66    ! [X0,X1] : (k1_xboole_0 != X0 => (k1_xboole_0 != k2_zfmisc_1(X0,k1_tarski(X1)) & k1_xboole_0 != k2_zfmisc_1(k1_tarski(X1),X0)))),
% 0.75/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).
% 0.75/0.66  fof(f93,plain,(
% 0.75/0.66    spl4_3 | spl4_4 | ~spl4_2),
% 0.75/0.66    inference(avatar_split_clause,[],[f84,f77,f90,f86])).
% 0.75/0.66  fof(f77,plain,(
% 0.75/0.66    spl4_2 <=> k1_xboole_0 = k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2))),
% 0.75/0.66    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.75/0.66  fof(f84,plain,(
% 0.75/0.66    k1_xboole_0 = sK1 | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl4_2),
% 0.75/0.66    inference(trivial_inequality_removal,[],[f83])).
% 0.75/0.66  fof(f83,plain,(
% 0.75/0.66    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK1 | k1_xboole_0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl4_2),
% 0.75/0.66    inference(superposition,[],[f35,f79])).
% 0.75/0.66  fof(f79,plain,(
% 0.75/0.66    k1_xboole_0 = k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | ~spl4_2),
% 0.75/0.66    inference(avatar_component_clause,[],[f77])).
% 0.75/0.66  fof(f80,plain,(
% 0.75/0.66    spl4_1 | spl4_2),
% 0.75/0.66    inference(avatar_split_clause,[],[f63,f77,f73])).
% 0.75/0.66  fof(f63,plain,(
% 0.75/0.66    k1_xboole_0 = k2_zfmisc_1(sK1,k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)) | k1_xboole_0 = k2_zfmisc_1(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2),sK1)),
% 0.75/0.66    inference(definition_unfolding,[],[f31,f62,f62])).
% 0.75/0.66  fof(f62,plain,(
% 0.75/0.66    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.75/0.66    inference(definition_unfolding,[],[f33,f61])).
% 0.75/0.66  fof(f61,plain,(
% 0.75/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.75/0.66    inference(definition_unfolding,[],[f34,f60])).
% 0.75/0.66  fof(f34,plain,(
% 0.75/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.75/0.66    inference(cnf_transformation,[],[f5])).
% 0.75/0.66  fof(f5,axiom,(
% 0.75/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.75/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.75/0.66  fof(f33,plain,(
% 0.75/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.75/0.66    inference(cnf_transformation,[],[f4])).
% 0.75/0.66  fof(f4,axiom,(
% 0.75/0.66    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.75/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.75/0.66  fof(f31,plain,(
% 0.75/0.66    k1_xboole_0 = k2_zfmisc_1(sK1,k1_tarski(sK2)) | k1_xboole_0 = k2_zfmisc_1(k1_tarski(sK2),sK1)),
% 0.75/0.66    inference(cnf_transformation,[],[f20])).
% 0.75/0.66  % SZS output end Proof for theBenchmark
% 0.75/0.66  % (15612)------------------------------
% 0.75/0.66  % (15612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.75/0.66  % (15612)Termination reason: Refutation
% 0.75/0.66  
% 0.75/0.66  % (15612)Memory used [KB]: 6268
% 0.75/0.66  % (15612)Time elapsed: 0.095 s
% 0.75/0.66  % (15612)------------------------------
% 0.75/0.66  % (15612)------------------------------
% 0.75/0.66  % (15463)Success in time 0.306 s
%------------------------------------------------------------------------------

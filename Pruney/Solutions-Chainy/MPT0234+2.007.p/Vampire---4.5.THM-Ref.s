%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:25 EST 2020

% Result     : Theorem 33.17s
% Output     : Refutation 33.17s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 185 expanded)
%              Number of leaves         :   25 (  82 expanded)
%              Depth                    :    8
%              Number of atoms          :  380 ( 761 expanded)
%              Number of equality atoms :  141 ( 325 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51644,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f91,f119,f142,f150,f154,f163,f253,f257,f274,f316,f1339,f3428,f3451,f26134,f49015,f50701,f51643])).

fof(f51643,plain,
    ( spl5_2
    | ~ spl5_10
    | ~ spl5_81
    | spl5_222
    | spl5_339
    | spl5_348 ),
    inference(avatar_contradiction_clause,[],[f51642])).

fof(f51642,plain,
    ( $false
    | spl5_2
    | ~ spl5_10
    | ~ spl5_81
    | spl5_222
    | spl5_339
    | spl5_348 ),
    inference(subsumption_resolution,[],[f49828,f51554])).

fof(f51554,plain,
    ( r2_hidden(sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK0))
    | spl5_2
    | ~ spl5_81
    | spl5_222
    | spl5_339
    | spl5_348 ),
    inference(unit_resulting_resolution,[],[f86,f26133,f49014,f50700,f3450])).

fof(f3450,plain,
    ( ! [X6,X4,X7,X5] :
        ( r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X7)
        | sK3(X4,X5,k5_xboole_0(X6,X7)) = X4
        | k2_tarski(X4,X5) = k5_xboole_0(X6,X7)
        | r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X6)
        | sK3(X4,X5,k5_xboole_0(X6,X7)) = X5 )
    | ~ spl5_81 ),
    inference(avatar_component_clause,[],[f3449])).

fof(f3449,plain,
    ( spl5_81
  <=> ! [X5,X7,X4,X6] :
        ( sK3(X4,X5,k5_xboole_0(X6,X7)) = X5
        | sK3(X4,X5,k5_xboole_0(X6,X7)) = X4
        | k2_tarski(X4,X5) = k5_xboole_0(X6,X7)
        | r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X6)
        | r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).

fof(f50700,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK1))
    | spl5_348 ),
    inference(avatar_component_clause,[],[f50698])).

fof(f50698,plain,
    ( spl5_348
  <=> r2_hidden(sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_348])])).

fof(f49014,plain,
    ( sK0 != sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl5_339 ),
    inference(avatar_component_clause,[],[f49012])).

fof(f49012,plain,
    ( spl5_339
  <=> sK0 = sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_339])])).

fof(f26133,plain,
    ( sK1 != sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl5_222 ),
    inference(avatar_component_clause,[],[f26131])).

fof(f26131,plain,
    ( spl5_222
  <=> sK1 = sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_222])])).

fof(f86,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_2
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f49828,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK0))
    | ~ spl5_10
    | spl5_339 ),
    inference(unit_resulting_resolution,[],[f49014,f118])).

fof(f118,plain,
    ( ! [X0,X3] :
        ( ~ r2_hidden(X3,k1_tarski(X0))
        | X0 = X3 )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl5_10
  <=> ! [X3,X0] :
        ( X0 = X3
        | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f50701,plain,
    ( ~ spl5_348
    | ~ spl5_10
    | spl5_222 ),
    inference(avatar_split_clause,[],[f27100,f26131,f117,f50698])).

fof(f27100,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK1))
    | ~ spl5_10
    | spl5_222 ),
    inference(unit_resulting_resolution,[],[f26133,f118])).

fof(f49015,plain,
    ( ~ spl5_339
    | spl5_2
    | ~ spl5_22
    | ~ spl5_78 ),
    inference(avatar_split_clause,[],[f3569,f3425,f255,f84,f49012])).

fof(f255,plain,
    ( spl5_22
  <=> ! [X1,X0,X2] :
        ( k2_tarski(X0,X1) = X2
        | sK3(X0,X1,X2) != X0
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f3425,plain,
    ( spl5_78
  <=> r2_hidden(sK0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).

fof(f3569,plain,
    ( sK0 != sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl5_2
    | ~ spl5_22
    | ~ spl5_78 ),
    inference(unit_resulting_resolution,[],[f86,f3427,f256])).

fof(f256,plain,
    ( ! [X2,X0,X1] :
        ( sK3(X0,X1,X2) != X0
        | k2_tarski(X0,X1) = X2
        | ~ r2_hidden(X0,X2) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f255])).

fof(f3427,plain,
    ( r2_hidden(sK0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl5_78 ),
    inference(avatar_component_clause,[],[f3425])).

fof(f26134,plain,
    ( ~ spl5_222
    | spl5_2
    | ~ spl5_21
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f1706,f1336,f251,f84,f26131])).

fof(f251,plain,
    ( spl5_21
  <=> ! [X1,X0,X2] :
        ( k2_tarski(X0,X1) = X2
        | sK3(X0,X1,X2) != X1
        | ~ r2_hidden(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f1336,plain,
    ( spl5_51
  <=> r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f1706,plain,
    ( sK1 != sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | spl5_2
    | ~ spl5_21
    | ~ spl5_51 ),
    inference(unit_resulting_resolution,[],[f86,f1338,f252])).

fof(f252,plain,
    ( ! [X2,X0,X1] :
        ( sK3(X0,X1,X2) != X1
        | k2_tarski(X0,X1) = X2
        | ~ r2_hidden(X1,X2) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f251])).

fof(f1338,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f1336])).

fof(f3451,plain,
    ( spl5_81
    | ~ spl5_13
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f318,f314,f140,f3449])).

fof(f140,plain,
    ( spl5_13
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X2)
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f314,plain,
    ( spl5_28
  <=> ! [X1,X0,X2] :
        ( k2_tarski(X0,X1) = X2
        | sK3(X0,X1,X2) = X1
        | sK3(X0,X1,X2) = X0
        | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f318,plain,
    ( ! [X6,X4,X7,X5] :
        ( sK3(X4,X5,k5_xboole_0(X6,X7)) = X5
        | sK3(X4,X5,k5_xboole_0(X6,X7)) = X4
        | k2_tarski(X4,X5) = k5_xboole_0(X6,X7)
        | r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X6)
        | r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X7) )
    | ~ spl5_13
    | ~ spl5_28 ),
    inference(resolution,[],[f315,f141])).

fof(f141,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
        | r2_hidden(X0,X1)
        | r2_hidden(X0,X2) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f315,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK3(X0,X1,X2),X2)
        | sK3(X0,X1,X2) = X1
        | sK3(X0,X1,X2) = X0
        | k2_tarski(X0,X1) = X2 )
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f314])).

fof(f3428,plain,
    ( spl5_78
    | ~ spl5_3
    | ~ spl5_15
    | spl5_25 ),
    inference(avatar_split_clause,[],[f328,f271,f148,f89,f3425])).

fof(f89,plain,
    ( spl5_3
  <=> ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f148,plain,
    ( spl5_15
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | r2_hidden(X0,X2)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f271,plain,
    ( spl5_25
  <=> r2_hidden(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f328,plain,
    ( r2_hidden(sK0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl5_3
    | ~ spl5_15
    | spl5_25 ),
    inference(unit_resulting_resolution,[],[f90,f273,f149])).

fof(f149,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | r2_hidden(X0,X2)
        | ~ r2_hidden(X0,X1) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f273,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | spl5_25 ),
    inference(avatar_component_clause,[],[f271])).

fof(f90,plain,
    ( ! [X3] : r2_hidden(X3,k1_tarski(X3))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f1339,plain,
    ( spl5_51
    | ~ spl5_3
    | ~ spl5_16
    | spl5_18 ),
    inference(avatar_split_clause,[],[f232,f160,f152,f89,f1336])).

fof(f152,plain,
    ( spl5_16
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f160,plain,
    ( spl5_18
  <=> r2_hidden(sK1,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f232,plain,
    ( r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))
    | ~ spl5_3
    | ~ spl5_16
    | spl5_18 ),
    inference(unit_resulting_resolution,[],[f90,f162,f153])).

fof(f153,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,X2) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f152])).

fof(f162,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | spl5_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f316,plain,(
    spl5_28 ),
    inference(avatar_split_clause,[],[f42,f314])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK3(X0,X1,X2) = X1
      | sK3(X0,X1,X2) = X0
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f274,plain,
    ( ~ spl5_25
    | spl5_1
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f128,f117,f79,f271])).

fof(f79,plain,
    ( spl5_1
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f128,plain,
    ( ~ r2_hidden(sK0,k1_tarski(sK1))
    | spl5_1
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f81,f118])).

fof(f81,plain,
    ( sK0 != sK1
    | spl5_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f257,plain,(
    spl5_22 ),
    inference(avatar_split_clause,[],[f74,f255])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK3(X0,X1,X2) != X0
      | ~ r2_hidden(X0,X2) ) ),
    inference(inner_rewriting,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK3(X0,X1,X2) != X0
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f253,plain,(
    spl5_21 ),
    inference(avatar_split_clause,[],[f73,f251])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK3(X0,X1,X2) != X1
      | ~ r2_hidden(X1,X2) ) ),
    inference(inner_rewriting,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = X2
      | sK3(X0,X1,X2) != X1
      | ~ r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f163,plain,
    ( ~ spl5_18
    | spl5_1
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f126,f117,f79,f160])).

fof(f126,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK0))
    | spl5_1
    | ~ spl5_10 ),
    inference(unit_resulting_resolution,[],[f81,f118])).

fof(f154,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f48,f152])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f150,plain,(
    spl5_15 ),
    inference(avatar_split_clause,[],[f47,f148])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f142,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f45,f140])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f119,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f59,f117])).

fof(f59,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f91,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f58,f89])).

fof(f58,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f31,f84])).

fof(f31,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
    & sK0 != sK1 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).

fof(f13,plain,
    ( ? [X0,X1] :
        ( k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
        & X0 != X1 )
   => ( k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))
      & sK0 != sK1 ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1))
      & X0 != X1 ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( X0 != X1
       => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( X0 != X1
     => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

fof(f82,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f30,f79])).

fof(f30,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:10:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.37  ipcrm: permission denied for id (803799040)
% 0.21/0.37  ipcrm: permission denied for id (803831810)
% 0.21/0.37  ipcrm: permission denied for id (803864580)
% 0.21/0.37  ipcrm: permission denied for id (806977541)
% 0.21/0.37  ipcrm: permission denied for id (803930118)
% 0.21/0.38  ipcrm: permission denied for id (807010311)
% 0.21/0.38  ipcrm: permission denied for id (803995657)
% 0.21/0.38  ipcrm: permission denied for id (807108619)
% 0.21/0.38  ipcrm: permission denied for id (807141388)
% 0.21/0.38  ipcrm: permission denied for id (807174157)
% 0.21/0.39  ipcrm: permission denied for id (807239695)
% 0.21/0.39  ipcrm: permission denied for id (807338001)
% 0.21/0.39  ipcrm: permission denied for id (807370770)
% 0.21/0.39  ipcrm: permission denied for id (807436308)
% 0.21/0.39  ipcrm: permission denied for id (804225045)
% 0.21/0.39  ipcrm: permission denied for id (804290582)
% 0.21/0.40  ipcrm: permission denied for id (804323351)
% 0.21/0.40  ipcrm: permission denied for id (804356120)
% 0.21/0.40  ipcrm: permission denied for id (807469081)
% 0.21/0.40  ipcrm: permission denied for id (807501850)
% 0.21/0.40  ipcrm: permission denied for id (804454427)
% 0.21/0.40  ipcrm: permission denied for id (804487196)
% 0.21/0.40  ipcrm: permission denied for id (807567390)
% 0.21/0.40  ipcrm: permission denied for id (804552735)
% 0.21/0.41  ipcrm: permission denied for id (807600160)
% 0.21/0.41  ipcrm: permission denied for id (804585505)
% 0.21/0.41  ipcrm: permission denied for id (804749350)
% 0.21/0.41  ipcrm: permission denied for id (807764007)
% 0.21/0.42  ipcrm: permission denied for id (807796776)
% 0.21/0.42  ipcrm: permission denied for id (807829545)
% 0.21/0.42  ipcrm: permission denied for id (804880426)
% 0.21/0.42  ipcrm: permission denied for id (807862315)
% 0.21/0.42  ipcrm: permission denied for id (804945964)
% 0.21/0.42  ipcrm: permission denied for id (804978733)
% 0.21/0.42  ipcrm: permission denied for id (805011502)
% 0.21/0.42  ipcrm: permission denied for id (805044271)
% 0.21/0.43  ipcrm: permission denied for id (807960625)
% 0.21/0.43  ipcrm: permission denied for id (808058932)
% 0.21/0.43  ipcrm: permission denied for id (805208117)
% 0.21/0.43  ipcrm: permission denied for id (808091702)
% 0.21/0.44  ipcrm: permission denied for id (805306425)
% 0.21/0.44  ipcrm: permission denied for id (805404732)
% 0.21/0.44  ipcrm: permission denied for id (808288318)
% 0.21/0.45  ipcrm: permission denied for id (808353856)
% 0.21/0.45  ipcrm: permission denied for id (805535810)
% 0.21/0.45  ipcrm: permission denied for id (808452164)
% 0.21/0.45  ipcrm: permission denied for id (808484933)
% 0.21/0.45  ipcrm: permission denied for id (808517702)
% 0.21/0.45  ipcrm: permission denied for id (805666888)
% 0.21/0.46  ipcrm: permission denied for id (805699657)
% 0.21/0.46  ipcrm: permission denied for id (808583242)
% 0.21/0.46  ipcrm: permission denied for id (805765195)
% 0.21/0.46  ipcrm: permission denied for id (805797964)
% 0.21/0.46  ipcrm: permission denied for id (805830733)
% 0.21/0.46  ipcrm: permission denied for id (805863503)
% 0.21/0.46  ipcrm: permission denied for id (805896272)
% 0.21/0.47  ipcrm: permission denied for id (805929041)
% 0.21/0.47  ipcrm: permission denied for id (808714324)
% 0.21/0.47  ipcrm: permission denied for id (805994581)
% 0.21/0.47  ipcrm: permission denied for id (806027351)
% 0.21/0.47  ipcrm: permission denied for id (808812632)
% 0.21/0.47  ipcrm: permission denied for id (806092889)
% 0.21/0.48  ipcrm: permission denied for id (808845402)
% 0.21/0.48  ipcrm: permission denied for id (808910940)
% 0.21/0.48  ipcrm: permission denied for id (806191198)
% 0.21/0.48  ipcrm: permission denied for id (806223967)
% 0.21/0.48  ipcrm: permission denied for id (808976480)
% 0.21/0.49  ipcrm: permission denied for id (806289506)
% 0.21/0.49  ipcrm: permission denied for id (809074788)
% 0.21/0.49  ipcrm: permission denied for id (806355045)
% 0.21/0.49  ipcrm: permission denied for id (809173096)
% 0.21/0.49  ipcrm: permission denied for id (809205865)
% 0.21/0.49  ipcrm: permission denied for id (809238634)
% 0.21/0.50  ipcrm: permission denied for id (806453355)
% 0.21/0.50  ipcrm: permission denied for id (809304173)
% 0.21/0.50  ipcrm: permission denied for id (809336942)
% 0.21/0.50  ipcrm: permission denied for id (809369711)
% 0.21/0.50  ipcrm: permission denied for id (809402480)
% 0.21/0.51  ipcrm: permission denied for id (806617203)
% 0.21/0.51  ipcrm: permission denied for id (809500788)
% 0.21/0.51  ipcrm: permission denied for id (809533557)
% 0.21/0.51  ipcrm: permission denied for id (809566326)
% 0.21/0.51  ipcrm: permission denied for id (806682743)
% 0.21/0.51  ipcrm: permission denied for id (806748280)
% 0.21/0.51  ipcrm: permission denied for id (806781049)
% 0.21/0.52  ipcrm: permission denied for id (809599098)
% 0.21/0.52  ipcrm: permission denied for id (806846590)
% 0.39/0.68  % (21867)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.39/0.70  % (21883)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.39/0.71  % (21875)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.39/0.72  % (21875)Refutation not found, incomplete strategy% (21875)------------------------------
% 0.39/0.72  % (21875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.72  % (21875)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.72  
% 0.39/0.72  % (21875)Memory used [KB]: 1663
% 0.39/0.72  % (21875)Time elapsed: 0.141 s
% 0.39/0.72  % (21875)------------------------------
% 0.39/0.72  % (21875)------------------------------
% 0.39/0.73  % (21877)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.39/0.73  % (21885)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.39/0.73  % (21865)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.45/0.73  % (21885)Refutation not found, incomplete strategy% (21885)------------------------------
% 0.45/0.73  % (21885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.45/0.73  % (21877)Refutation not found, incomplete strategy% (21877)------------------------------
% 0.45/0.73  % (21877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.45/0.73  % (21869)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.45/0.73  % (21878)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.45/0.73  % (21877)Termination reason: Refutation not found, incomplete strategy
% 0.45/0.73  
% 0.45/0.73  % (21877)Memory used [KB]: 10618
% 0.45/0.73  % (21877)Time elapsed: 0.079 s
% 0.45/0.73  % (21877)------------------------------
% 0.45/0.73  % (21877)------------------------------
% 0.45/0.73  % (21885)Termination reason: Refutation not found, incomplete strategy
% 0.45/0.73  
% 0.45/0.73  % (21885)Memory used [KB]: 10618
% 0.45/0.73  % (21885)Time elapsed: 0.070 s
% 0.45/0.73  % (21885)------------------------------
% 0.45/0.73  % (21885)------------------------------
% 0.45/0.73  % (21878)Refutation not found, incomplete strategy% (21878)------------------------------
% 0.45/0.73  % (21878)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.45/0.74  % (21886)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.45/0.74  % (21863)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.45/0.74  % (21878)Termination reason: Refutation not found, incomplete strategy
% 0.45/0.74  
% 0.45/0.74  % (21878)Memory used [KB]: 1663
% 0.45/0.74  % (21878)Time elapsed: 0.148 s
% 0.45/0.74  % (21878)------------------------------
% 0.45/0.74  % (21878)------------------------------
% 0.45/0.74  % (21881)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.45/0.74  % (21870)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.45/0.75  % (21868)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.45/0.75  % (21889)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.45/0.75  % (21861)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.45/0.76  % (21872)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.45/0.76  % (21871)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.45/0.76  % (21864)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.45/0.76  % (21873)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.45/0.76  % (21879)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.45/0.76  % (21879)Refutation not found, incomplete strategy% (21879)------------------------------
% 0.45/0.76  % (21879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.45/0.76  % (21862)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.45/0.76  % (21879)Termination reason: Refutation not found, incomplete strategy
% 0.45/0.76  
% 0.45/0.76  % (21879)Memory used [KB]: 1663
% 0.45/0.76  % (21879)Time elapsed: 0.170 s
% 0.45/0.76  % (21879)------------------------------
% 0.45/0.76  % (21879)------------------------------
% 0.45/0.76  % (21862)Refutation not found, incomplete strategy% (21862)------------------------------
% 0.45/0.76  % (21862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.45/0.76  % (21862)Termination reason: Refutation not found, incomplete strategy
% 0.45/0.76  
% 0.45/0.76  % (21862)Memory used [KB]: 1663
% 0.45/0.76  % (21862)Time elapsed: 0.174 s
% 0.45/0.76  % (21862)------------------------------
% 0.45/0.76  % (21862)------------------------------
% 0.45/0.76  % (21882)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.45/0.76  % (21888)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.45/0.77  % (21876)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.45/0.77  % (21866)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.45/0.77  % (21890)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.45/0.77  % (21887)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.45/0.77  % (21888)Refutation not found, incomplete strategy% (21888)------------------------------
% 0.45/0.77  % (21888)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.45/0.77  % (21887)Refutation not found, incomplete strategy% (21887)------------------------------
% 0.45/0.77  % (21887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.45/0.77  % (21874)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.45/0.77  % (21890)Refutation not found, incomplete strategy% (21890)------------------------------
% 0.45/0.77  % (21890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.45/0.77  % (21887)Termination reason: Refutation not found, incomplete strategy
% 0.45/0.77  
% 0.45/0.77  % (21887)Memory used [KB]: 6140
% 0.45/0.77  % (21887)Time elapsed: 0.180 s
% 0.45/0.77  % (21887)------------------------------
% 0.45/0.77  % (21887)------------------------------
% 0.45/0.77  % (21890)Termination reason: Refutation not found, incomplete strategy
% 0.45/0.77  
% 0.45/0.77  % (21890)Memory used [KB]: 1663
% 0.45/0.77  % (21890)Time elapsed: 0.184 s
% 0.45/0.77  % (21890)------------------------------
% 0.45/0.77  % (21890)------------------------------
% 0.45/0.77  % (21880)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.45/0.77  % (21888)Termination reason: Refutation not found, incomplete strategy
% 0.45/0.77  
% 0.45/0.77  % (21888)Memory used [KB]: 6140
% 0.45/0.77  % (21888)Time elapsed: 0.176 s
% 0.45/0.77  % (21888)------------------------------
% 0.45/0.77  % (21888)------------------------------
% 0.45/0.78  % (21884)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.92/0.83  % (21891)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 0.92/0.87  % (21902)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 0.92/0.88  % (21897)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 0.92/0.88  % (21864)Refutation not found, incomplete strategy% (21864)------------------------------
% 0.92/0.88  % (21864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.92/0.88  % (21864)Termination reason: Refutation not found, incomplete strategy
% 0.92/0.88  
% 0.92/0.88  % (21864)Memory used [KB]: 6140
% 0.92/0.88  % (21864)Time elapsed: 0.284 s
% 0.92/0.88  % (21864)------------------------------
% 0.92/0.88  % (21864)------------------------------
% 0.92/0.88  % (21903)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 0.92/0.89  % (21916)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 0.92/0.89  % (21916)Refutation not found, incomplete strategy% (21916)------------------------------
% 0.92/0.89  % (21916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.92/0.89  % (21916)Termination reason: Refutation not found, incomplete strategy
% 0.92/0.89  
% 0.92/0.89  % (21916)Memory used [KB]: 10618
% 0.92/0.89  % (21916)Time elapsed: 0.100 s
% 0.92/0.89  % (21916)------------------------------
% 0.92/0.89  % (21916)------------------------------
% 1.07/0.89  % (21922)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 1.07/0.89  % (21917)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 1.07/0.90  % (21921)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 1.07/0.91  % (21926)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 1.07/1.01  % (21863)Time limit reached!
% 1.07/1.01  % (21863)------------------------------
% 1.07/1.01  % (21863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.07/1.01  % (21863)Termination reason: Time limit
% 1.07/1.01  % (21863)Termination phase: Saturation
% 1.07/1.01  
% 1.07/1.01  % (21863)Memory used [KB]: 7036
% 1.07/1.01  % (21863)Time elapsed: 0.400 s
% 1.07/1.01  % (21863)------------------------------
% 1.07/1.01  % (21863)------------------------------
% 1.07/1.02  % (21980)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 1.07/1.02  % (21980)Refutation not found, incomplete strategy% (21980)------------------------------
% 1.07/1.02  % (21980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.07/1.02  % (21980)Termination reason: Refutation not found, incomplete strategy
% 1.07/1.02  
% 1.07/1.02  % (21980)Memory used [KB]: 10746
% 1.07/1.02  % (21980)Time elapsed: 0.094 s
% 1.07/1.02  % (21980)------------------------------
% 1.07/1.02  % (21980)------------------------------
% 1.07/1.03  % (21988)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 4.15/1.09  % (21867)Time limit reached!
% 4.15/1.09  % (21867)------------------------------
% 4.15/1.09  % (21867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.15/1.09  % (21867)Termination reason: Time limit
% 4.15/1.09  % (21867)Termination phase: Saturation
% 4.15/1.09  
% 4.15/1.09  % (21867)Memory used [KB]: 13688
% 4.15/1.09  % (21867)Time elapsed: 0.500 s
% 4.15/1.09  % (21867)------------------------------
% 4.15/1.09  % (21867)------------------------------
% 4.88/1.14  % (22059)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 4.88/1.15  % (22060)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 4.88/1.20  % (22078)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 5.40/1.22  % (22078)Refutation not found, incomplete strategy% (22078)------------------------------
% 5.40/1.22  % (22078)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.40/1.22  % (22078)Termination reason: Refutation not found, incomplete strategy
% 5.40/1.22  
% 5.40/1.22  % (22078)Memory used [KB]: 10746
% 5.40/1.22  % (22078)Time elapsed: 0.105 s
% 5.40/1.22  % (22078)------------------------------
% 5.40/1.22  % (22078)------------------------------
% 5.40/1.23  % (21868)Time limit reached!
% 5.40/1.23  % (21868)------------------------------
% 5.40/1.23  % (21868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.40/1.23  % (21868)Termination reason: Time limit
% 5.40/1.23  % (21868)Termination phase: Saturation
% 5.40/1.23  
% 5.40/1.23  % (21868)Memory used [KB]: 4349
% 5.40/1.23  % (21868)Time elapsed: 0.600 s
% 5.40/1.23  % (21868)------------------------------
% 5.40/1.23  % (21868)------------------------------
% 5.92/1.32  % (22133)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 6.63/1.38  % (22136)lrs+1010_3:2_awrs=decay:awrsf=2:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:bs=on:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:nm=6:newcnf=on:nwc=1.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:s2a=on:sos=on:sac=on:sp=weighted_frequency:urr=on_1 on theBenchmark
% 6.87/1.42  % (21921)Time limit reached!
% 6.87/1.42  % (21921)------------------------------
% 6.87/1.42  % (21921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.87/1.42  % (21921)Termination reason: Time limit
% 6.87/1.42  
% 6.87/1.42  % (21921)Memory used [KB]: 17014
% 6.87/1.42  % (21921)Time elapsed: 0.624 s
% 6.87/1.42  % (21921)------------------------------
% 6.87/1.42  % (21921)------------------------------
% 7.64/1.56  % (22137)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_2 on theBenchmark
% 8.11/1.59  % (21873)Time limit reached!
% 8.11/1.59  % (21873)------------------------------
% 8.11/1.59  % (21873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.11/1.59  % (21873)Termination reason: Time limit
% 8.11/1.59  
% 8.11/1.59  % (21873)Memory used [KB]: 12409
% 8.11/1.59  % (21873)Time elapsed: 1.012 s
% 8.11/1.59  % (21873)------------------------------
% 8.11/1.59  % (21873)------------------------------
% 8.76/1.67  % (22136)Time limit reached!
% 8.76/1.67  % (22136)------------------------------
% 8.76/1.67  % (22136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.76/1.67  % (22136)Termination reason: Time limit
% 8.76/1.67  
% 8.76/1.67  % (22136)Memory used [KB]: 8187
% 8.76/1.67  % (22136)Time elapsed: 0.419 s
% 8.76/1.67  % (22136)------------------------------
% 8.76/1.67  % (22136)------------------------------
% 9.35/1.73  % (22138)lrs+2_1_add=large:afp=100000:afq=1.0:amm=off:anc=none:bd=off:bs=unit_only:bsr=on:gsp=input_only:lma=on:lwlo=on:newcnf=on:nwc=1:stl=30:sos=theory:sp=reverse_arity:updr=off_1 on theBenchmark
% 9.70/1.79  % (22139)lrs+1010_2:3_afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:gs=on:gsem=off:nm=16:nwc=1:nicw=on:sas=z3:stl=30:sd=2:ss=axioms:st=1.5:updr=off_97 on theBenchmark
% 9.70/1.80  % (21902)Time limit reached!
% 9.70/1.80  % (21902)------------------------------
% 9.70/1.80  % (21902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.16/1.80  % (21902)Termination reason: Time limit
% 10.16/1.80  % (21902)Termination phase: Saturation
% 10.16/1.80  
% 10.16/1.80  % (21902)Memory used [KB]: 8571
% 10.16/1.80  % (21902)Time elapsed: 0.800 s
% 10.16/1.80  % (21902)------------------------------
% 10.16/1.80  % (21902)------------------------------
% 10.16/1.82  % (21861)Time limit reached!
% 10.16/1.82  % (21861)------------------------------
% 10.16/1.82  % (21861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.16/1.82  % (21861)Termination reason: Time limit
% 10.16/1.82  
% 10.16/1.82  % (21861)Memory used [KB]: 4605
% 10.16/1.82  % (21861)Time elapsed: 1.232 s
% 10.16/1.82  % (21861)------------------------------
% 10.16/1.82  % (21861)------------------------------
% 10.62/1.89  % (21866)Time limit reached!
% 10.62/1.89  % (21866)------------------------------
% 10.62/1.89  % (21866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.62/1.89  % (21866)Termination reason: Time limit
% 10.62/1.89  
% 10.62/1.89  % (21866)Memory used [KB]: 5884
% 10.62/1.89  % (21866)Time elapsed: 1.310 s
% 10.62/1.89  % (21866)------------------------------
% 10.62/1.89  % (21866)------------------------------
% 10.62/1.93  % (22140)dis+10_3_av=off:irw=on:nm=0:nwc=1:sd=1:ss=axioms:st=5.0:sos=all:sp=occurrence:updr=off_1 on theBenchmark
% 10.62/1.94  % (22141)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 11.31/1.95  % (22137)Time limit reached!
% 11.31/1.95  % (22137)------------------------------
% 11.31/1.95  % (22137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.31/1.96  % (22137)Termination reason: Time limit
% 11.31/1.96  
% 11.31/1.96  % (22137)Memory used [KB]: 7803
% 11.31/1.96  % (22137)Time elapsed: 0.506 s
% 11.31/1.96  % (22137)------------------------------
% 11.31/1.96  % (22137)------------------------------
% 11.66/2.02  % (22138)Time limit reached!
% 11.66/2.02  % (22138)------------------------------
% 11.66/2.02  % (22138)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.66/2.03  % (22138)Termination reason: Time limit
% 11.66/2.03  
% 11.66/2.03  % (22138)Memory used [KB]: 7164
% 11.66/2.03  % (22138)Time elapsed: 0.407 s
% 11.66/2.03  % (22138)------------------------------
% 11.66/2.03  % (22138)------------------------------
% 12.88/2.24  % (22140)Time limit reached!
% 12.88/2.24  % (22140)------------------------------
% 12.88/2.24  % (22140)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.88/2.24  % (22140)Termination reason: Time limit
% 12.88/2.24  % (22140)Termination phase: Saturation
% 12.88/2.24  
% 12.88/2.24  % (22140)Memory used [KB]: 2814
% 12.88/2.24  % (22140)Time elapsed: 0.400 s
% 12.88/2.24  % (22140)------------------------------
% 12.88/2.24  % (22140)------------------------------
% 12.88/2.25  % (22141)Time limit reached!
% 12.88/2.25  % (22141)------------------------------
% 12.88/2.25  % (22141)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.88/2.25  % (22141)Termination reason: Time limit
% 12.88/2.25  % (22141)Termination phase: Saturation
% 12.88/2.25  
% 12.88/2.25  % (22141)Memory used [KB]: 9083
% 12.88/2.25  % (22141)Time elapsed: 0.400 s
% 12.88/2.25  % (22141)------------------------------
% 12.88/2.25  % (22141)------------------------------
% 15.38/2.47  % (21881)Time limit reached!
% 15.38/2.47  % (21881)------------------------------
% 15.38/2.47  % (21881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 15.38/2.47  % (21881)Termination reason: Time limit
% 15.38/2.47  
% 15.38/2.47  % (21881)Memory used [KB]: 17270
% 15.38/2.47  % (21881)Time elapsed: 1.864 s
% 15.38/2.47  % (21881)------------------------------
% 15.38/2.47  % (21881)------------------------------
% 19.40/3.00  % (21876)Time limit reached!
% 19.40/3.00  % (21876)------------------------------
% 19.40/3.00  % (21876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 19.40/3.00  % (21876)Termination reason: Time limit
% 19.40/3.00  
% 19.40/3.00  % (21876)Memory used [KB]: 12409
% 19.40/3.00  % (21876)Time elapsed: 2.420 s
% 19.40/3.00  % (21876)------------------------------
% 19.40/3.00  % (21876)------------------------------
% 25.25/3.71  % (21872)Time limit reached!
% 25.25/3.71  % (21872)------------------------------
% 25.25/3.71  % (21872)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.25/3.71  % (21872)Termination reason: Time limit
% 25.25/3.71  % (21872)Termination phase: Saturation
% 25.25/3.71  
% 25.25/3.71  % (21872)Memory used [KB]: 35308
% 25.25/3.71  % (21872)Time elapsed: 3.100 s
% 25.25/3.71  % (21872)------------------------------
% 25.25/3.71  % (21872)------------------------------
% 25.93/3.78  % (21869)Time limit reached!
% 25.93/3.78  % (21869)------------------------------
% 25.93/3.78  % (21869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 25.93/3.78  % (21869)Termination reason: Time limit
% 25.93/3.78  
% 25.93/3.78  % (21869)Memory used [KB]: 10746
% 25.93/3.78  % (21869)Time elapsed: 3.125 s
% 25.93/3.78  % (21869)------------------------------
% 25.93/3.78  % (21869)------------------------------
% 26.51/3.91  % (21926)Time limit reached!
% 26.51/3.91  % (21926)------------------------------
% 26.51/3.91  % (21926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 26.51/3.91  % (21926)Termination reason: Time limit
% 26.51/3.91  
% 26.51/3.91  % (21926)Memory used [KB]: 36332
% 26.51/3.91  % (21926)Time elapsed: 3.047 s
% 26.51/3.91  % (21926)------------------------------
% 26.51/3.91  % (21926)------------------------------
% 27.29/3.95  % (21880)Time limit reached!
% 27.29/3.95  % (21880)------------------------------
% 27.29/3.95  % (21880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 27.29/3.95  % (21880)Termination reason: Time limit
% 27.29/3.95  
% 27.29/3.95  % (21880)Memory used [KB]: 29935
% 27.29/3.95  % (21880)Time elapsed: 3.337 s
% 27.29/3.95  % (21880)------------------------------
% 27.29/3.95  % (21880)------------------------------
% 28.62/4.12  % (21922)Time limit reached!
% 28.62/4.12  % (21922)------------------------------
% 28.62/4.12  % (21922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 28.62/4.12  % (21922)Termination reason: Time limit
% 28.62/4.12  
% 28.62/4.12  % (21922)Memory used [KB]: 14328
% 28.62/4.12  % (21922)Time elapsed: 3.310 s
% 28.62/4.12  % (21922)------------------------------
% 28.62/4.12  % (21922)------------------------------
% 28.89/4.18  % (21903)Time limit reached!
% 28.89/4.18  % (21903)------------------------------
% 28.89/4.18  % (21903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 28.89/4.18  % (21903)Termination reason: Time limit
% 28.89/4.18  % (21903)Termination phase: Saturation
% 28.89/4.18  
% 28.89/4.18  % (21903)Memory used [KB]: 48997
% 28.89/4.18  % (21903)Time elapsed: 3.400 s
% 28.89/4.18  % (21903)------------------------------
% 28.89/4.18  % (21903)------------------------------
% 33.17/4.67  % (21891)Refutation found. Thanks to Tanya!
% 33.17/4.67  % SZS status Theorem for theBenchmark
% 33.17/4.67  % SZS output start Proof for theBenchmark
% 33.17/4.67  fof(f51644,plain,(
% 33.17/4.67    $false),
% 33.17/4.67    inference(avatar_sat_refutation,[],[f82,f87,f91,f119,f142,f150,f154,f163,f253,f257,f274,f316,f1339,f3428,f3451,f26134,f49015,f50701,f51643])).
% 33.17/4.67  fof(f51643,plain,(
% 33.17/4.67    spl5_2 | ~spl5_10 | ~spl5_81 | spl5_222 | spl5_339 | spl5_348),
% 33.17/4.67    inference(avatar_contradiction_clause,[],[f51642])).
% 33.17/4.67  fof(f51642,plain,(
% 33.17/4.67    $false | (spl5_2 | ~spl5_10 | ~spl5_81 | spl5_222 | spl5_339 | spl5_348)),
% 33.17/4.67    inference(subsumption_resolution,[],[f49828,f51554])).
% 33.17/4.67  fof(f51554,plain,(
% 33.17/4.67    r2_hidden(sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK0)) | (spl5_2 | ~spl5_81 | spl5_222 | spl5_339 | spl5_348)),
% 33.17/4.67    inference(unit_resulting_resolution,[],[f86,f26133,f49014,f50700,f3450])).
% 33.17/4.67  fof(f3450,plain,(
% 33.17/4.67    ( ! [X6,X4,X7,X5] : (r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X7) | sK3(X4,X5,k5_xboole_0(X6,X7)) = X4 | k2_tarski(X4,X5) = k5_xboole_0(X6,X7) | r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X6) | sK3(X4,X5,k5_xboole_0(X6,X7)) = X5) ) | ~spl5_81),
% 33.17/4.67    inference(avatar_component_clause,[],[f3449])).
% 33.17/4.67  fof(f3449,plain,(
% 33.17/4.67    spl5_81 <=> ! [X5,X7,X4,X6] : (sK3(X4,X5,k5_xboole_0(X6,X7)) = X5 | sK3(X4,X5,k5_xboole_0(X6,X7)) = X4 | k2_tarski(X4,X5) = k5_xboole_0(X6,X7) | r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X6) | r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X7))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_81])])).
% 33.17/4.67  fof(f50700,plain,(
% 33.17/4.67    ~r2_hidden(sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK1)) | spl5_348),
% 33.17/4.67    inference(avatar_component_clause,[],[f50698])).
% 33.17/4.67  fof(f50698,plain,(
% 33.17/4.67    spl5_348 <=> r2_hidden(sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK1))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_348])])).
% 33.17/4.67  fof(f49014,plain,(
% 33.17/4.67    sK0 != sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | spl5_339),
% 33.17/4.67    inference(avatar_component_clause,[],[f49012])).
% 33.17/4.67  fof(f49012,plain,(
% 33.17/4.67    spl5_339 <=> sK0 = sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_339])])).
% 33.17/4.67  fof(f26133,plain,(
% 33.17/4.67    sK1 != sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | spl5_222),
% 33.17/4.67    inference(avatar_component_clause,[],[f26131])).
% 33.17/4.67  fof(f26131,plain,(
% 33.17/4.67    spl5_222 <=> sK1 = sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_222])])).
% 33.17/4.67  fof(f86,plain,(
% 33.17/4.67    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) | spl5_2),
% 33.17/4.67    inference(avatar_component_clause,[],[f84])).
% 33.17/4.67  fof(f84,plain,(
% 33.17/4.67    spl5_2 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 33.17/4.67  fof(f49828,plain,(
% 33.17/4.67    ~r2_hidden(sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK0)) | (~spl5_10 | spl5_339)),
% 33.17/4.67    inference(unit_resulting_resolution,[],[f49014,f118])).
% 33.17/4.67  fof(f118,plain,(
% 33.17/4.67    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) ) | ~spl5_10),
% 33.17/4.67    inference(avatar_component_clause,[],[f117])).
% 33.17/4.67  fof(f117,plain,(
% 33.17/4.67    spl5_10 <=> ! [X3,X0] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0)))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 33.17/4.67  fof(f50701,plain,(
% 33.17/4.67    ~spl5_348 | ~spl5_10 | spl5_222),
% 33.17/4.67    inference(avatar_split_clause,[],[f27100,f26131,f117,f50698])).
% 33.17/4.67  fof(f27100,plain,(
% 33.17/4.67    ~r2_hidden(sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),k1_tarski(sK1)) | (~spl5_10 | spl5_222)),
% 33.17/4.67    inference(unit_resulting_resolution,[],[f26133,f118])).
% 33.17/4.67  fof(f49015,plain,(
% 33.17/4.67    ~spl5_339 | spl5_2 | ~spl5_22 | ~spl5_78),
% 33.17/4.67    inference(avatar_split_clause,[],[f3569,f3425,f255,f84,f49012])).
% 33.17/4.67  fof(f255,plain,(
% 33.17/4.67    spl5_22 <=> ! [X1,X0,X2] : (k2_tarski(X0,X1) = X2 | sK3(X0,X1,X2) != X0 | ~r2_hidden(X0,X2))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 33.17/4.67  fof(f3425,plain,(
% 33.17/4.67    spl5_78 <=> r2_hidden(sK0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_78])])).
% 33.17/4.67  fof(f3569,plain,(
% 33.17/4.67    sK0 != sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | (spl5_2 | ~spl5_22 | ~spl5_78)),
% 33.17/4.67    inference(unit_resulting_resolution,[],[f86,f3427,f256])).
% 33.17/4.67  fof(f256,plain,(
% 33.17/4.67    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) != X0 | k2_tarski(X0,X1) = X2 | ~r2_hidden(X0,X2)) ) | ~spl5_22),
% 33.17/4.67    inference(avatar_component_clause,[],[f255])).
% 33.17/4.67  fof(f3427,plain,(
% 33.17/4.67    r2_hidden(sK0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | ~spl5_78),
% 33.17/4.67    inference(avatar_component_clause,[],[f3425])).
% 33.17/4.67  fof(f26134,plain,(
% 33.17/4.67    ~spl5_222 | spl5_2 | ~spl5_21 | ~spl5_51),
% 33.17/4.67    inference(avatar_split_clause,[],[f1706,f1336,f251,f84,f26131])).
% 33.17/4.67  fof(f251,plain,(
% 33.17/4.67    spl5_21 <=> ! [X1,X0,X2] : (k2_tarski(X0,X1) = X2 | sK3(X0,X1,X2) != X1 | ~r2_hidden(X1,X2))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 33.17/4.67  fof(f1336,plain,(
% 33.17/4.67    spl5_51 <=> r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 33.17/4.67  fof(f1706,plain,(
% 33.17/4.67    sK1 != sK3(sK0,sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | (spl5_2 | ~spl5_21 | ~spl5_51)),
% 33.17/4.67    inference(unit_resulting_resolution,[],[f86,f1338,f252])).
% 33.17/4.67  fof(f252,plain,(
% 33.17/4.67    ( ! [X2,X0,X1] : (sK3(X0,X1,X2) != X1 | k2_tarski(X0,X1) = X2 | ~r2_hidden(X1,X2)) ) | ~spl5_21),
% 33.17/4.67    inference(avatar_component_clause,[],[f251])).
% 33.17/4.67  fof(f1338,plain,(
% 33.17/4.67    r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | ~spl5_51),
% 33.17/4.67    inference(avatar_component_clause,[],[f1336])).
% 33.17/4.67  fof(f3451,plain,(
% 33.17/4.67    spl5_81 | ~spl5_13 | ~spl5_28),
% 33.17/4.67    inference(avatar_split_clause,[],[f318,f314,f140,f3449])).
% 33.17/4.67  fof(f140,plain,(
% 33.17/4.67    spl5_13 <=> ! [X1,X0,X2] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2)))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 33.17/4.67  fof(f314,plain,(
% 33.17/4.67    spl5_28 <=> ! [X1,X0,X2] : (k2_tarski(X0,X1) = X2 | sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 33.17/4.67  fof(f318,plain,(
% 33.17/4.67    ( ! [X6,X4,X7,X5] : (sK3(X4,X5,k5_xboole_0(X6,X7)) = X5 | sK3(X4,X5,k5_xboole_0(X6,X7)) = X4 | k2_tarski(X4,X5) = k5_xboole_0(X6,X7) | r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X6) | r2_hidden(sK3(X4,X5,k5_xboole_0(X6,X7)),X7)) ) | (~spl5_13 | ~spl5_28)),
% 33.17/4.67    inference(resolution,[],[f315,f141])).
% 33.17/4.67  fof(f141,plain,(
% 33.17/4.67    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | r2_hidden(X0,X2)) ) | ~spl5_13),
% 33.17/4.67    inference(avatar_component_clause,[],[f140])).
% 33.17/4.67  fof(f315,plain,(
% 33.17/4.67    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | k2_tarski(X0,X1) = X2) ) | ~spl5_28),
% 33.17/4.67    inference(avatar_component_clause,[],[f314])).
% 33.17/4.67  fof(f3428,plain,(
% 33.17/4.67    spl5_78 | ~spl5_3 | ~spl5_15 | spl5_25),
% 33.17/4.67    inference(avatar_split_clause,[],[f328,f271,f148,f89,f3425])).
% 33.17/4.67  fof(f89,plain,(
% 33.17/4.67    spl5_3 <=> ! [X3] : r2_hidden(X3,k1_tarski(X3))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 33.17/4.67  fof(f148,plain,(
% 33.17/4.67    spl5_15 <=> ! [X1,X0,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 33.17/4.67  fof(f271,plain,(
% 33.17/4.67    spl5_25 <=> r2_hidden(sK0,k1_tarski(sK1))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 33.17/4.67  fof(f328,plain,(
% 33.17/4.67    r2_hidden(sK0,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | (~spl5_3 | ~spl5_15 | spl5_25)),
% 33.17/4.67    inference(unit_resulting_resolution,[],[f90,f273,f149])).
% 33.17/4.67  fof(f149,plain,(
% 33.17/4.67    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) ) | ~spl5_15),
% 33.17/4.67    inference(avatar_component_clause,[],[f148])).
% 33.17/4.67  fof(f273,plain,(
% 33.17/4.67    ~r2_hidden(sK0,k1_tarski(sK1)) | spl5_25),
% 33.17/4.67    inference(avatar_component_clause,[],[f271])).
% 33.17/4.67  fof(f90,plain,(
% 33.17/4.67    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) ) | ~spl5_3),
% 33.17/4.67    inference(avatar_component_clause,[],[f89])).
% 33.17/4.67  fof(f1339,plain,(
% 33.17/4.67    spl5_51 | ~spl5_3 | ~spl5_16 | spl5_18),
% 33.17/4.67    inference(avatar_split_clause,[],[f232,f160,f152,f89,f1336])).
% 33.17/4.67  fof(f152,plain,(
% 33.17/4.67    spl5_16 <=> ! [X1,X0,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 33.17/4.67  fof(f160,plain,(
% 33.17/4.67    spl5_18 <=> r2_hidden(sK1,k1_tarski(sK0))),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 33.17/4.67  fof(f232,plain,(
% 33.17/4.67    r2_hidden(sK1,k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))) | (~spl5_3 | ~spl5_16 | spl5_18)),
% 33.17/4.67    inference(unit_resulting_resolution,[],[f90,f162,f153])).
% 33.17/4.67  fof(f153,plain,(
% 33.17/4.67    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) ) | ~spl5_16),
% 33.17/4.67    inference(avatar_component_clause,[],[f152])).
% 33.17/4.67  fof(f162,plain,(
% 33.17/4.67    ~r2_hidden(sK1,k1_tarski(sK0)) | spl5_18),
% 33.17/4.67    inference(avatar_component_clause,[],[f160])).
% 33.17/4.67  fof(f316,plain,(
% 33.17/4.67    spl5_28),
% 33.17/4.67    inference(avatar_split_clause,[],[f42,f314])).
% 33.17/4.67  fof(f42,plain,(
% 33.17/4.67    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 33.17/4.67    inference(cnf_transformation,[],[f23])).
% 33.17/4.67  fof(f23,plain,(
% 33.17/4.67    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 33.17/4.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 33.17/4.67  fof(f22,plain,(
% 33.17/4.67    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 33.17/4.67    introduced(choice_axiom,[])).
% 33.17/4.67  fof(f21,plain,(
% 33.17/4.67    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 33.17/4.67    inference(rectify,[],[f20])).
% 33.17/4.67  fof(f20,plain,(
% 33.17/4.67    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 33.17/4.67    inference(flattening,[],[f19])).
% 33.17/4.67  fof(f19,plain,(
% 33.17/4.67    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 33.17/4.67    inference(nnf_transformation,[],[f4])).
% 33.17/4.67  fof(f4,axiom,(
% 33.17/4.67    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 33.17/4.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 33.17/4.67  fof(f274,plain,(
% 33.17/4.67    ~spl5_25 | spl5_1 | ~spl5_10),
% 33.17/4.67    inference(avatar_split_clause,[],[f128,f117,f79,f271])).
% 33.17/4.67  fof(f79,plain,(
% 33.17/4.67    spl5_1 <=> sK0 = sK1),
% 33.17/4.67    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 33.17/4.67  fof(f128,plain,(
% 33.17/4.67    ~r2_hidden(sK0,k1_tarski(sK1)) | (spl5_1 | ~spl5_10)),
% 33.17/4.67    inference(unit_resulting_resolution,[],[f81,f118])).
% 33.17/4.67  fof(f81,plain,(
% 33.17/4.67    sK0 != sK1 | spl5_1),
% 33.17/4.67    inference(avatar_component_clause,[],[f79])).
% 33.17/4.67  fof(f257,plain,(
% 33.17/4.67    spl5_22),
% 33.17/4.67    inference(avatar_split_clause,[],[f74,f255])).
% 33.17/4.67  fof(f74,plain,(
% 33.17/4.67    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK3(X0,X1,X2) != X0 | ~r2_hidden(X0,X2)) )),
% 33.17/4.67    inference(inner_rewriting,[],[f43])).
% 33.17/4.67  fof(f43,plain,(
% 33.17/4.67    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK3(X0,X1,X2) != X0 | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 33.17/4.67    inference(cnf_transformation,[],[f23])).
% 33.17/4.67  fof(f253,plain,(
% 33.17/4.67    spl5_21),
% 33.17/4.67    inference(avatar_split_clause,[],[f73,f251])).
% 33.17/4.67  fof(f73,plain,(
% 33.17/4.67    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK3(X0,X1,X2) != X1 | ~r2_hidden(X1,X2)) )),
% 33.17/4.67    inference(inner_rewriting,[],[f44])).
% 33.17/4.67  fof(f44,plain,(
% 33.17/4.67    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = X2 | sK3(X0,X1,X2) != X1 | ~r2_hidden(sK3(X0,X1,X2),X2)) )),
% 33.17/4.67    inference(cnf_transformation,[],[f23])).
% 33.17/4.67  fof(f163,plain,(
% 33.17/4.67    ~spl5_18 | spl5_1 | ~spl5_10),
% 33.17/4.67    inference(avatar_split_clause,[],[f126,f117,f79,f160])).
% 33.17/4.67  fof(f126,plain,(
% 33.17/4.67    ~r2_hidden(sK1,k1_tarski(sK0)) | (spl5_1 | ~spl5_10)),
% 33.17/4.67    inference(unit_resulting_resolution,[],[f81,f118])).
% 33.17/4.67  fof(f154,plain,(
% 33.17/4.67    spl5_16),
% 33.17/4.67    inference(avatar_split_clause,[],[f48,f152])).
% 33.17/4.67  fof(f48,plain,(
% 33.17/4.67    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 33.17/4.67    inference(cnf_transformation,[],[f24])).
% 33.17/4.67  fof(f24,plain,(
% 33.17/4.67    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 33.17/4.67    inference(nnf_transformation,[],[f11])).
% 33.17/4.67  fof(f11,plain,(
% 33.17/4.67    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 33.17/4.67    inference(ennf_transformation,[],[f1])).
% 33.17/4.67  fof(f1,axiom,(
% 33.17/4.67    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 33.17/4.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 33.17/4.67  fof(f150,plain,(
% 33.17/4.67    spl5_15),
% 33.17/4.67    inference(avatar_split_clause,[],[f47,f148])).
% 33.17/4.67  fof(f47,plain,(
% 33.17/4.67    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 33.17/4.67    inference(cnf_transformation,[],[f24])).
% 33.17/4.67  fof(f142,plain,(
% 33.17/4.67    spl5_13),
% 33.17/4.67    inference(avatar_split_clause,[],[f45,f140])).
% 33.17/4.67  fof(f45,plain,(
% 33.17/4.67    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 33.17/4.67    inference(cnf_transformation,[],[f24])).
% 33.17/4.67  fof(f119,plain,(
% 33.17/4.67    spl5_10),
% 33.17/4.67    inference(avatar_split_clause,[],[f59,f117])).
% 33.17/4.67  fof(f59,plain,(
% 33.17/4.67    ( ! [X0,X3] : (X0 = X3 | ~r2_hidden(X3,k1_tarski(X0))) )),
% 33.17/4.67    inference(equality_resolution,[],[f34])).
% 33.17/4.67  fof(f34,plain,(
% 33.17/4.67    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 33.17/4.67    inference(cnf_transformation,[],[f18])).
% 33.17/4.67  fof(f18,plain,(
% 33.17/4.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 33.17/4.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f17])).
% 33.17/4.67  fof(f17,plain,(
% 33.17/4.67    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 33.17/4.67    introduced(choice_axiom,[])).
% 33.17/4.67  fof(f16,plain,(
% 33.17/4.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 33.17/4.67    inference(rectify,[],[f15])).
% 33.17/4.67  fof(f15,plain,(
% 33.17/4.67    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 33.17/4.67    inference(nnf_transformation,[],[f3])).
% 33.17/4.67  fof(f3,axiom,(
% 33.17/4.67    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 33.17/4.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 33.17/4.67  fof(f91,plain,(
% 33.17/4.67    spl5_3),
% 33.17/4.67    inference(avatar_split_clause,[],[f58,f89])).
% 33.17/4.67  fof(f58,plain,(
% 33.17/4.67    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 33.17/4.67    inference(equality_resolution,[],[f57])).
% 33.17/4.67  fof(f57,plain,(
% 33.17/4.67    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 33.17/4.67    inference(equality_resolution,[],[f35])).
% 33.17/4.67  fof(f35,plain,(
% 33.17/4.67    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 33.17/4.67    inference(cnf_transformation,[],[f18])).
% 33.17/4.67  fof(f87,plain,(
% 33.17/4.67    ~spl5_2),
% 33.17/4.67    inference(avatar_split_clause,[],[f31,f84])).
% 33.17/4.67  fof(f31,plain,(
% 33.17/4.67    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1))),
% 33.17/4.67    inference(cnf_transformation,[],[f14])).
% 33.17/4.67  fof(f14,plain,(
% 33.17/4.67    k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) & sK0 != sK1),
% 33.17/4.67    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f13])).
% 33.17/4.67  fof(f13,plain,(
% 33.17/4.67    ? [X0,X1] : (k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1) => (k2_tarski(sK0,sK1) != k5_xboole_0(k1_tarski(sK0),k1_tarski(sK1)) & sK0 != sK1)),
% 33.17/4.67    introduced(choice_axiom,[])).
% 33.17/4.67  fof(f10,plain,(
% 33.17/4.67    ? [X0,X1] : (k2_tarski(X0,X1) != k5_xboole_0(k1_tarski(X0),k1_tarski(X1)) & X0 != X1)),
% 33.17/4.67    inference(ennf_transformation,[],[f9])).
% 33.17/4.67  fof(f9,negated_conjecture,(
% 33.17/4.67    ~! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 33.17/4.67    inference(negated_conjecture,[],[f8])).
% 33.17/4.67  fof(f8,conjecture,(
% 33.17/4.67    ! [X0,X1] : (X0 != X1 => k2_tarski(X0,X1) = k5_xboole_0(k1_tarski(X0),k1_tarski(X1)))),
% 33.17/4.67    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).
% 33.17/4.67  fof(f82,plain,(
% 33.17/4.67    ~spl5_1),
% 33.17/4.67    inference(avatar_split_clause,[],[f30,f79])).
% 33.17/4.67  fof(f30,plain,(
% 33.17/4.67    sK0 != sK1),
% 33.17/4.67    inference(cnf_transformation,[],[f14])).
% 33.17/4.67  % SZS output end Proof for theBenchmark
% 33.17/4.67  % (21891)------------------------------
% 33.17/4.67  % (21891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 33.17/4.67  % (21891)Termination reason: Refutation
% 33.17/4.67  
% 33.17/4.67  % (21891)Memory used [KB]: 73431
% 33.17/4.67  % (21891)Time elapsed: 3.867 s
% 33.17/4.67  % (21891)------------------------------
% 33.17/4.67  % (21891)------------------------------
% 33.17/4.68  % (21690)Success in time 4.325 s
%------------------------------------------------------------------------------

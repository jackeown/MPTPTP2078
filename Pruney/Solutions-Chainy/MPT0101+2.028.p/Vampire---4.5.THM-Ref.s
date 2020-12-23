%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:56 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 186 expanded)
%              Number of leaves         :   13 (  75 expanded)
%              Depth                    :   10
%              Number of atoms          :  317 ( 822 expanded)
%              Number of equality atoms :   32 (  87 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f321,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f82,f83,f121,f172,f194,f195,f196,f199,f245,f247,f318,f320])).

fof(f320,plain,
    ( ~ spl6_5
    | spl6_4
    | spl6_1 ),
    inference(avatar_split_clause,[],[f104,f70,f114,f118])).

fof(f118,plain,
    ( spl6_5
  <=> r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f114,plain,
    ( spl6_4
  <=> r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f70,plain,
    ( spl6_1
  <=> r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f104,plain,
    ( r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | spl6_1 ),
    inference(resolution,[],[f71,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f71,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f318,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | spl6_5 ),
    inference(avatar_split_clause,[],[f309,f118,f78,f74])).

fof(f74,plain,
    ( spl6_2
  <=> r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f78,plain,
    ( spl6_3
  <=> r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f309,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | spl6_5 ),
    inference(resolution,[],[f119,f47])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).

fof(f18,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f119,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | spl6_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f247,plain,
    ( ~ spl6_3
    | spl6_2
    | spl6_4 ),
    inference(avatar_split_clause,[],[f163,f114,f74,f78])).

fof(f163,plain,
    ( r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | spl6_4 ),
    inference(resolution,[],[f116,f46])).

fof(f116,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f245,plain,
    ( spl6_4
    | spl6_5
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f235,f70,f118,f114])).

fof(f235,plain,
    ( r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1))
    | ~ spl6_1 ),
    inference(resolution,[],[f72,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f72,plain,
    ( r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f199,plain,
    ( spl6_2
    | spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f173,f114,f78,f74])).

fof(f173,plain,
    ( r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f115,f43])).

fof(f115,plain,
    ( r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f196,plain,
    ( spl6_2
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f184,f118,f74])).

fof(f184,plain,
    ( r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_5 ),
    inference(resolution,[],[f120,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f120,plain,
    ( r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f195,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f174,f114,f78,f74])).

fof(f174,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f115,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f194,plain,
    ( spl6_3
    | ~ spl6_5 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl6_3
    | ~ spl6_5 ),
    inference(resolution,[],[f120,f98])).

fof(f98,plain,
    ( ! [X4] : ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(X4,sK1))
    | spl6_3 ),
    inference(resolution,[],[f79,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f79,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f172,plain,
    ( ~ spl6_2
    | spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f162,f114,f78,f74])).

fof(f162,plain,
    ( r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | spl6_4 ),
    inference(resolution,[],[f116,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f121,plain,
    ( ~ spl6_4
    | spl6_5
    | spl6_1 ),
    inference(avatar_split_clause,[],[f103,f70,f118,f114])).

fof(f103,plain,
    ( r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1))
    | spl6_1 ),
    inference(resolution,[],[f71,f45])).

fof(f83,plain,
    ( ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f68,f78,f70])).

fof(f68,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f54,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f42,f53])).

fof(f53,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & ~ r2_hidden(sK4(X0,X1,X2),X0) )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( r2_hidden(sK4(X0,X1,X2),X1)
            | r2_hidden(sK4(X0,X1,X2),X0)
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).

fof(f23,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & ~ r2_hidden(sK4(X0,X1,X2),X0) )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( r2_hidden(sK4(X0,X1,X2),X1)
          | r2_hidden(sK4(X0,X1,X2),X0)
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
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
    inference(rectify,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f54,plain,(
    ~ sQ5_eqProxy(k2_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(equality_proxy_replacement,[],[f26,f53])).

fof(f26,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f82,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f67,f74,f70])).

fof(f67,plain,
    ( ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | ~ r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f54,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k2_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f41,f53])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f81,plain,
    ( spl6_1
    | spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f66,f78,f74,f70])).

fof(f66,plain,
    ( r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)
    | r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)
    | r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f54,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k2_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f40,f53])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:11:00 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (519)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (518)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (527)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (517)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (527)Refutation not found, incomplete strategy% (527)------------------------------
% 0.21/0.47  % (527)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (526)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (527)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (527)Memory used [KB]: 6140
% 0.21/0.47  % (527)Time elapsed: 0.057 s
% 0.21/0.47  % (527)------------------------------
% 0.21/0.47  % (527)------------------------------
% 0.21/0.48  % (512)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (512)Refutation not found, incomplete strategy% (512)------------------------------
% 0.21/0.48  % (512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (512)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (512)Memory used [KB]: 6140
% 0.21/0.48  % (512)Time elapsed: 0.065 s
% 0.21/0.48  % (512)------------------------------
% 0.21/0.48  % (512)------------------------------
% 0.21/0.48  % (516)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (524)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (513)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (532)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (513)Refutation not found, incomplete strategy% (513)------------------------------
% 0.21/0.48  % (513)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (513)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (513)Memory used [KB]: 10490
% 0.21/0.48  % (513)Time elapsed: 0.072 s
% 0.21/0.48  % (513)------------------------------
% 0.21/0.48  % (513)------------------------------
% 0.21/0.48  % (532)Refutation not found, incomplete strategy% (532)------------------------------
% 0.21/0.48  % (532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (532)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (532)Memory used [KB]: 10618
% 0.21/0.48  % (532)Time elapsed: 0.077 s
% 0.21/0.48  % (532)------------------------------
% 0.21/0.48  % (532)------------------------------
% 0.21/0.48  % (523)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (525)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (525)Refutation not found, incomplete strategy% (525)------------------------------
% 0.21/0.48  % (525)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (525)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (525)Memory used [KB]: 1535
% 0.21/0.48  % (525)Time elapsed: 0.076 s
% 0.21/0.48  % (525)------------------------------
% 0.21/0.48  % (525)------------------------------
% 0.21/0.49  % (523)Refutation not found, incomplete strategy% (523)------------------------------
% 0.21/0.49  % (523)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (523)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (523)Memory used [KB]: 10618
% 0.21/0.49  % (523)Time elapsed: 0.078 s
% 0.21/0.49  % (523)------------------------------
% 0.21/0.49  % (523)------------------------------
% 0.21/0.49  % (520)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (526)Refutation not found, incomplete strategy% (526)------------------------------
% 0.21/0.49  % (526)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (526)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (526)Memory used [KB]: 10618
% 0.21/0.49  % (526)Time elapsed: 0.038 s
% 0.21/0.49  % (526)------------------------------
% 0.21/0.49  % (526)------------------------------
% 0.21/0.49  % (522)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (514)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (521)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (531)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (524)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f321,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f81,f82,f83,f121,f172,f194,f195,f196,f199,f245,f247,f318,f320])).
% 0.21/0.50  fof(f320,plain,(
% 0.21/0.50    ~spl6_5 | spl6_4 | spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f104,f70,f114,f118])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    spl6_5 <=> r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl6_4 <=> r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    spl6_1 <=> r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) | spl6_1),
% 0.21/0.50    inference(resolution,[],[f71,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.21/0.50    inference(nnf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) | spl6_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f70])).
% 0.21/0.50  fof(f318,plain,(
% 0.21/0.50    ~spl6_2 | ~spl6_3 | spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f309,f118,f78,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl6_2 <=> r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    spl6_3 <=> r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.50  fof(f309,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | spl6_5),
% 0.21/0.50    inference(resolution,[],[f119,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f17,f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(rectify,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(flattening,[],[f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) | spl6_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f118])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    ~spl6_3 | spl6_2 | spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f163,f114,f74,f78])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | spl6_4),
% 0.21/0.50    inference(resolution,[],[f116,f46])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1)) | spl6_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f114])).
% 0.21/0.50  fof(f245,plain,(
% 0.21/0.50    spl6_4 | spl6_5 | ~spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f235,f70,f118,f114])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) | r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1)) | ~spl6_1),
% 0.21/0.50    inference(resolution,[],[f72,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) | ~spl6_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f70])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    spl6_2 | spl6_3 | ~spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f173,f114,f78,f74])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | ~spl6_4),
% 0.21/0.50    inference(resolution,[],[f115,f43])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1)) | ~spl6_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f114])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    spl6_2 | ~spl6_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f184,f118,f74])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | ~spl6_5),
% 0.21/0.50    inference(resolution,[],[f120,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) | ~spl6_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f118])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    ~spl6_2 | ~spl6_3 | ~spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f174,f114,f78,f74])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | ~spl6_4),
% 0.21/0.50    inference(resolution,[],[f115,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    spl6_3 | ~spl6_5),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f183])).
% 0.21/0.50  fof(f183,plain,(
% 0.21/0.50    $false | (spl6_3 | ~spl6_5)),
% 0.21/0.50    inference(resolution,[],[f120,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ( ! [X4] : (~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(X4,sK1))) ) | spl6_3),
% 0.21/0.50    inference(resolution,[],[f79,f48])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,k3_xboole_0(X0,X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | spl6_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f78])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ~spl6_2 | spl6_3 | spl6_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f162,f114,f78,f74])).
% 0.21/0.50  fof(f162,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | spl6_4),
% 0.21/0.50    inference(resolution,[],[f116,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ~spl6_4 | spl6_5 | spl6_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f103,f70,f118,f114])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) | ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(sK0,sK1)) | spl6_1),
% 0.21/0.50    inference(resolution,[],[f71,f45])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ~spl6_1 | ~spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f68,f78,f70])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 0.21/0.50    inference(resolution,[],[f54,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sQ5_eqProxy(k2_xboole_0(X0,X1),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f42,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ! [X1,X0] : (sQ5_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.50    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f22,f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK4(X0,X1,X2),X1) & ~r2_hidden(sK4(X0,X1,X2),X0)) | ~r2_hidden(sK4(X0,X1,X2),X2)) & (r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(rectify,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 0.21/0.50    inference(nnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ~sQ5_eqProxy(k2_xboole_0(sK0,sK1),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f26,f53])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f7,plain,(
% 0.21/0.50    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.50    inference(negated_conjecture,[],[f5])).
% 0.21/0.50  fof(f5,conjecture,(
% 0.21/0.50    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    ~spl6_1 | ~spl6_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f67,f74,f70])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | ~r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 0.21/0.50    inference(resolution,[],[f54,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sQ5_eqProxy(k2_xboole_0(X0,X1),X2) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f41,f53])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    spl6_1 | spl6_2 | spl6_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f66,f78,f74,f70])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK1) | r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),sK0) | r2_hidden(sK4(sK0,sK1,k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 0.21/0.50    inference(resolution,[],[f54,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (sQ5_eqProxy(k2_xboole_0(X0,X1),X2) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(equality_proxy_replacement,[],[f40,f53])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k2_xboole_0(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f24])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (524)------------------------------
% 0.21/0.50  % (524)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (524)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (524)Memory used [KB]: 6140
% 0.21/0.50  % (524)Time elapsed: 0.057 s
% 0.21/0.50  % (524)------------------------------
% 0.21/0.50  % (524)------------------------------
% 0.21/0.50  % (511)Success in time 0.143 s
%------------------------------------------------------------------------------

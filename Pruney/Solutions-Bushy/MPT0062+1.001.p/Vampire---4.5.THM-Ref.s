%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0062+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 280 expanded)
%              Number of leaves         :   16 ( 105 expanded)
%              Depth                    :    9
%              Number of atoms          :  416 (1666 expanded)
%              Number of equality atoms :   47 ( 207 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f266,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f80,f81,f98,f162,f201,f202,f203,f205,f245,f246,f257,f259,f260,f261,f262,f263,f265])).

fof(f265,plain,
    ( ~ spl6_4
    | spl6_2 ),
    inference(avatar_split_clause,[],[f100,f72,f91])).

fof(f91,plain,
    ( spl6_4
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f72,plain,
    ( spl6_2
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f100,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK0)
    | spl6_2 ),
    inference(resolution,[],[f73,f47])).

fof(f47,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f16,f17])).

fof(f17,plain,(
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

fof(f16,plain,(
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
    inference(rectify,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f73,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(sK0,sK1))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f263,plain,
    ( spl6_5
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f250,f77,f95])).

fof(f95,plain,
    ( spl6_5
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f77,plain,
    ( spl6_3
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f250,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f78,f44])).

fof(f44,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
            | ~ r2_hidden(sK2(X0,X1,X2),X0)
            | ~ r2_hidden(sK2(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK2(X0,X1,X2),X1)
              & r2_hidden(sK2(X0,X1,X2),X0) )
            | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f11,f12])).

fof(f12,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK2(X0,X1,X2),X1)
          | ~ r2_hidden(sK2(X0,X1,X2),X0)
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(sK2(X0,X1,X2),X0) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
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
    inference(rectify,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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

fof(f78,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f262,plain,
    ( spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f145,f125,f91])).

fof(f125,plain,
    ( spl6_6
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f145,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK0)
    | ~ spl6_6 ),
    inference(resolution,[],[f127,f51])).

fof(f51,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f127,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK0,sK1))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f261,plain,
    ( ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f146,f125,f95])).

fof(f146,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1)
    | ~ spl6_6 ),
    inference(resolution,[],[f127,f50])).

fof(f50,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f260,plain,
    ( ~ spl6_5
    | spl6_4
    | spl6_7 ),
    inference(avatar_split_clause,[],[f236,f129,f91,f95])).

fof(f129,plain,
    ( spl6_7
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f236,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK0)
    | ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1)
    | spl6_7 ),
    inference(resolution,[],[f130,f49])).

fof(f49,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f130,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,sK0))
    | spl6_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f259,plain,
    ( spl6_6
    | spl6_7
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f117,f68,f129,f125])).

fof(f68,plain,
    ( spl6_1
  <=> r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f117,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,sK0))
    | r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK0,sK1))
    | ~ spl6_1 ),
    inference(resolution,[],[f70,f48])).

fof(f48,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f257,plain,
    ( spl6_4
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f249,f77,f91])).

fof(f249,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f78,f45])).

fof(f45,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f246,plain,
    ( ~ spl6_5
    | spl6_2 ),
    inference(avatar_split_clause,[],[f101,f72,f95])).

fof(f101,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1)
    | spl6_2 ),
    inference(resolution,[],[f73,f46])).

fof(f46,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k2_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f245,plain,
    ( ~ spl6_7
    | spl6_1 ),
    inference(avatar_split_clause,[],[f186,f68,f129])).

fof(f186,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,sK0))
    | spl6_1 ),
    inference(resolution,[],[f69,f46])).

fof(f69,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f205,plain,
    ( ~ spl6_4
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f155,f129,f91])).

fof(f155,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK0)
    | ~ spl6_7 ),
    inference(resolution,[],[f131,f50])).

fof(f131,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK1,sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f203,plain,
    ( ~ spl6_4
    | spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f193,f125,f95,f91])).

fof(f193,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1)
    | ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK0)
    | spl6_6 ),
    inference(resolution,[],[f126,f49])).

fof(f126,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK0,sK1))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f202,plain,
    ( ~ spl6_4
    | ~ spl6_5
    | spl6_3 ),
    inference(avatar_split_clause,[],[f109,f77,f95,f91])).

fof(f109,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1)
    | ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK0)
    | spl6_3 ),
    inference(resolution,[],[f79,f43])).

fof(f43,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f27])).

fof(f27,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f79,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f201,plain,
    ( ~ spl6_6
    | spl6_1 ),
    inference(avatar_split_clause,[],[f185,f68,f125])).

fof(f185,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(sK0,sK1))
    | spl6_1 ),
    inference(resolution,[],[f69,f47])).

fof(f162,plain,
    ( spl6_5
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f154,f129,f95])).

fof(f154,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f131,f51])).

fof(f98,plain,
    ( spl6_4
    | spl6_5
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f83,f72,f95,f91])).

fof(f83,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK1)
    | r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f74,f48])).

fof(f74,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(sK0,sK1))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f81,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f66,f77,f72,f68])).

fof(f66,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(sK0,sK1))
    | ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    inference(resolution,[],[f53,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f42,f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( sQ5_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ5_eqProxy])])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | ~ r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f53,plain,(
    ~ sQ5_eqProxy(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    inference(equality_proxy_replacement,[],[f24,f52])).

fof(f24,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f80,plain,
    ( spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f65,f77,f68])).

fof(f65,plain,
    ( ~ r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))
    | r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    inference(resolution,[],[f53,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k4_xboole_0(X0,X1),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f41,f52])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f75,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f64,f72,f68])).

fof(f64,plain,
    ( r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(sK0,sK1))
    | r2_hidden(sK4(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) ),
    inference(resolution,[],[f53,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sQ5_eqProxy(k4_xboole_0(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(equality_proxy_replacement,[],[f40,f52])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f23])).

%------------------------------------------------------------------------------

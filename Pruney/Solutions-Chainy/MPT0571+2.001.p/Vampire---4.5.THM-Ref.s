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
% DateTime   : Thu Dec  3 12:50:39 EST 2020

% Result     : Theorem 2.76s
% Output     : Refutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 323 expanded)
%              Number of leaves         :   22 ( 121 expanded)
%              Depth                    :   11
%              Number of atoms          :  419 (1424 expanded)
%              Number of equality atoms :   38 ( 204 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2452,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f110,f116,f252,f255,f256,f587,f659,f1094,f1096,f2305,f2352,f2361,f2451])).

fof(f2451,plain,
    ( spl9_17
    | ~ spl9_13
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f2442,f249,f217,f276])).

fof(f276,plain,
    ( spl9_17
  <=> r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).

fof(f217,plain,
    ( spl9_13
  <=> r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).

fof(f249,plain,
    ( spl9_15
  <=> ! [X0] :
        ( ~ r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),X0)
        | r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f2442,plain,
    ( r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK1))
    | ~ spl9_13
    | ~ spl9_15 ),
    inference(resolution,[],[f250,f219])).

fof(f219,plain,
    ( r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK1)
    | ~ spl9_13 ),
    inference(avatar_component_clause,[],[f217])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),X0)
        | r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,X0)) )
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f249])).

fof(f2361,plain,
    ( spl9_12
    | spl9_13
    | ~ spl9_4 ),
    inference(avatar_split_clause,[],[f206,f107,f217,f213])).

fof(f213,plain,
    ( spl9_12
  <=> r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f107,plain,
    ( spl9_4
  <=> r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f206,plain,
    ( r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK1)
    | r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK0)
    | ~ spl9_4 ),
    inference(resolution,[],[f109,f58])).

fof(f58,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2 ) ),
    inference(definition_unfolding,[],[f40,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f40,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
              & ~ r2_hidden(sK7(X0,X1,X2),X0) )
            | ~ r2_hidden(sK7(X0,X1,X2),X2) )
          & ( r2_hidden(sK7(X0,X1,X2),X1)
            | r2_hidden(sK7(X0,X1,X2),X0)
            | r2_hidden(sK7(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK7(X0,X1,X2),X1)
            & ~ r2_hidden(sK7(X0,X1,X2),X0) )
          | ~ r2_hidden(sK7(X0,X1,X2),X2) )
        & ( r2_hidden(sK7(X0,X1,X2),X1)
          | r2_hidden(sK7(X0,X1,X2),X0)
          | r2_hidden(sK7(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
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
    inference(rectify,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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

fof(f109,plain,
    ( r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f2352,plain,
    ( ~ spl9_17
    | ~ spl9_5
    | ~ spl9_17 ),
    inference(avatar_split_clause,[],[f2347,f276,f112,f276])).

fof(f112,plain,
    ( spl9_5
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
        | ~ r2_hidden(k4_tarski(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f2347,plain,
    ( ~ r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK1))
    | ~ spl9_5
    | ~ spl9_17 ),
    inference(resolution,[],[f1064,f79])).

fof(f79,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK6(X3,X4,sK2),k5_xboole_0(X5,k4_xboole_0(X4,X5)))
      | ~ r2_hidden(X3,k10_relat_1(sK2,X4)) ) ),
    inference(resolution,[],[f70,f56])).

fof(f56,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2 ) ),
    inference(definition_unfolding,[],[f42,f35])).

fof(f42,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f70,plain,(
    ! [X4,X5] :
      ( r2_hidden(sK6(X4,X5,sK2),X5)
      | ~ r2_hidden(X4,k10_relat_1(sK2,X5)) ) ),
    inference(resolution,[],[f27,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ( r2_hidden(sK6(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
            & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f20])).

fof(f20,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X0,X4),X2)
          & r2_hidden(X4,k2_relat_1(X2)) )
     => ( r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
        & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X0,X4),X2)
              & r2_hidden(X4,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k10_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X0,X3),X2)
              | ~ r2_hidden(X3,k2_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X0,X3),X2)
              & r2_hidden(X3,k2_relat_1(X2)) )
          | ~ r2_hidden(X0,k10_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

fof(f27,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k10_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k10_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_relat_1(X2) )
   => ( k10_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(f1064,plain,
    ( ~ r2_hidden(sK6(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK1,sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | ~ spl9_5
    | ~ spl9_17 ),
    inference(resolution,[],[f257,f278])).

fof(f278,plain,
    ( r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK1))
    | ~ spl9_17 ),
    inference(avatar_component_clause,[],[f276])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,X0))
        | ~ r2_hidden(sK6(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),X0,sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) )
    | ~ spl9_5 ),
    inference(resolution,[],[f113,f69])).

fof(f69,plain,(
    ! [X2,X3] :
      ( r2_hidden(k4_tarski(X2,sK6(X2,X3,sK2)),sK2)
      | ~ r2_hidden(X2,k10_relat_1(sK2,X3)) ) ),
    inference(resolution,[],[f27,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2)
      | ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),X0),sK2)
        | ~ r2_hidden(X0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) )
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f2305,plain,
    ( ~ spl9_16
    | ~ spl9_5
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f2300,f272,f112,f272])).

fof(f272,plain,
    ( spl9_16
  <=> r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f2300,plain,
    ( ~ r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK0))
    | ~ spl9_5
    | ~ spl9_16 ),
    inference(resolution,[],[f1063,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,sK2),k5_xboole_0(X1,k4_xboole_0(X2,X1)))
      | ~ r2_hidden(X0,k10_relat_1(sK2,X1)) ) ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0)))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2 ) ),
    inference(definition_unfolding,[],[f41,f35])).

fof(f41,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X0)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1063,plain,
    ( ~ r2_hidden(sK6(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK0,sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | ~ spl9_5
    | ~ spl9_16 ),
    inference(resolution,[],[f257,f274])).

fof(f274,plain,
    ( r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK0))
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f272])).

fof(f1096,plain,
    ( ~ spl9_17
    | spl9_2 ),
    inference(avatar_split_clause,[],[f224,f98,f276])).

fof(f98,plain,
    ( spl9_2
  <=> r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f224,plain,
    ( ~ r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK1))
    | spl9_2 ),
    inference(resolution,[],[f99,f56])).

fof(f99,plain,
    ( ~ r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f1094,plain,
    ( spl9_16
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f991,f249,f213,f272])).

fof(f991,plain,
    ( r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK0))
    | ~ spl9_12
    | ~ spl9_15 ),
    inference(resolution,[],[f250,f215])).

fof(f215,plain,
    ( r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK0)
    | ~ spl9_12 ),
    inference(avatar_component_clause,[],[f213])).

fof(f659,plain,
    ( spl9_16
    | spl9_17
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f265,f98,f276,f272])).

fof(f265,plain,
    ( r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK1))
    | r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK0))
    | ~ spl9_2 ),
    inference(resolution,[],[f100,f58])).

fof(f100,plain,
    ( r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f587,plain,
    ( ~ spl9_16
    | spl9_2 ),
    inference(avatar_split_clause,[],[f223,f98,f272])).

fof(f223,plain,
    ( ~ r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK0))
    | spl9_2 ),
    inference(resolution,[],[f99,f57])).

fof(f256,plain,
    ( spl9_2
    | spl9_3 ),
    inference(avatar_split_clause,[],[f205,f102,f98])).

fof(f102,plain,
    ( spl9_3
  <=> r2_hidden(k4_tarski(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f205,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))))),sK2)
    | r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))) ),
    inference(resolution,[],[f77,f60])).

fof(f60,plain,(
    ~ sQ8_eqProxy(k10_relat_1(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))) ),
    inference(equality_proxy_replacement,[],[f46,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( sQ8_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).

fof(f46,plain,(
    k10_relat_1(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) != k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))) ),
    inference(definition_unfolding,[],[f28,f35,f35])).

fof(f28,plain,(
    k10_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f77,plain,(
    ! [X21,X22] :
      ( sQ8_eqProxy(k10_relat_1(sK2,X21),X22)
      | r2_hidden(k4_tarski(sK3(sK2,X21,X22),sK4(sK2,X21,X22)),sK2)
      | r2_hidden(sK3(sK2,X21,X22),X22) ) ),
    inference(resolution,[],[f27,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sQ8_eqProxy(k10_relat_1(X0,X1),X2)
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f32,f59])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
                | ~ r2_hidden(sK3(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK4(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) )
                | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ( r2_hidden(sK5(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f13,f16,f15,f14])).

fof(f14,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X3,X4),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X3,X5),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X6,X8),X0) )
     => ( r2_hidden(sK5(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X3,X5),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X6,X7),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X6,X8),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X3,X4),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X3,X4),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).

fof(f255,plain,
    ( ~ spl9_2
    | spl9_5 ),
    inference(avatar_split_clause,[],[f197,f112,f98])).

fof(f197,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
      | ~ r2_hidden(k4_tarski(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),X0),sK2)
      | ~ r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))) ) ),
    inference(resolution,[],[f75,f60])).

fof(f75,plain,(
    ! [X17,X18,X16] :
      ( sQ8_eqProxy(k10_relat_1(sK2,X16),X17)
      | ~ r2_hidden(X18,X16)
      | ~ r2_hidden(k4_tarski(sK3(sK2,X16,X17),X18),sK2)
      | ~ r2_hidden(sK3(sK2,X16,X17),X17) ) ),
    inference(resolution,[],[f27,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X1] :
      ( sQ8_eqProxy(k10_relat_1(X0,X1),X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f34,f59])).

fof(f34,plain,(
    ! [X4,X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f252,plain,
    ( spl9_15
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f235,f102,f249])).

fof(f235,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),X1)
        | r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,X1)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f104,f72])).

fof(f72,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(k4_tarski(X9,X11),sK2)
      | ~ r2_hidden(X11,X10)
      | r2_hidden(X9,k10_relat_1(sK2,X10)) ) ),
    inference(resolution,[],[f27,f53])).

fof(f53,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k10_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X6,X7),X0)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f104,plain,
    ( r2_hidden(k4_tarski(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))))),sK2)
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f102])).

fof(f116,plain,(
    spl9_1 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl9_1 ),
    inference(resolution,[],[f96,f27])).

fof(f96,plain,
    ( ~ v1_relat_1(sK2)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl9_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f110,plain,
    ( ~ spl9_1
    | spl9_2
    | spl9_4 ),
    inference(avatar_split_clause,[],[f91,f107,f98,f94])).

fof(f91,plain,
    ( r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))
    | r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f60,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( sQ8_eqProxy(k10_relat_1(X0,X1),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f33,f59])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X0,X1) = X2
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 11:21:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (2158)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (2140)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (2150)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (2142)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (2138)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.54  % (2137)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.31/0.54  % (2143)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.31/0.54  % (2136)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.31/0.54  % (2161)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.54  % (2162)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.55  % (2139)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.31/0.55  % (2137)Refutation not found, incomplete strategy% (2137)------------------------------
% 1.31/0.55  % (2137)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (2137)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (2137)Memory used [KB]: 10618
% 1.31/0.55  % (2137)Time elapsed: 0.126 s
% 1.31/0.55  % (2137)------------------------------
% 1.31/0.55  % (2137)------------------------------
% 1.31/0.55  % (2163)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.31/0.55  % (2141)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.55  % (2154)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.55  % (2164)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.31/0.55  % (2153)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.31/0.55  % (2160)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.31/0.55  % (2151)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.31/0.55  % (2146)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.48/0.56  % (2156)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.48/0.56  % (2155)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.48/0.56  % (2135)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.48/0.56  % (2145)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.48/0.56  % (2145)Refutation not found, incomplete strategy% (2145)------------------------------
% 1.48/0.56  % (2145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (2145)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (2145)Memory used [KB]: 10618
% 1.48/0.56  % (2145)Time elapsed: 0.140 s
% 1.48/0.56  % (2145)------------------------------
% 1.48/0.56  % (2145)------------------------------
% 1.48/0.56  % (2144)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.48/0.56  % (2148)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.48/0.56  % (2147)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.56  % (2159)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.48/0.56  % (2152)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.48/0.57  % (2152)Refutation not found, incomplete strategy% (2152)------------------------------
% 1.48/0.57  % (2152)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (2152)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (2152)Memory used [KB]: 10618
% 1.48/0.57  % (2152)Time elapsed: 0.148 s
% 1.48/0.57  % (2152)------------------------------
% 1.48/0.57  % (2152)------------------------------
% 1.48/0.57  % (2157)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.48/0.57  % (2160)Refutation not found, incomplete strategy% (2160)------------------------------
% 1.48/0.57  % (2160)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (2160)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (2160)Memory used [KB]: 6268
% 1.48/0.57  % (2160)Time elapsed: 0.161 s
% 1.48/0.57  % (2160)------------------------------
% 1.48/0.57  % (2160)------------------------------
% 1.48/0.60  % (2157)Refutation not found, incomplete strategy% (2157)------------------------------
% 1.48/0.60  % (2157)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.60  % (2149)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.48/0.61  % (2157)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.61  
% 1.48/0.61  % (2157)Memory used [KB]: 10746
% 1.48/0.61  % (2157)Time elapsed: 0.157 s
% 1.48/0.61  % (2157)------------------------------
% 1.48/0.61  % (2157)------------------------------
% 2.30/0.69  % (2186)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.30/0.72  % (2188)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.30/0.73  % (2187)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.30/0.74  % (2189)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.76/0.74  % (2150)Refutation found. Thanks to Tanya!
% 2.76/0.74  % SZS status Theorem for theBenchmark
% 2.76/0.74  % SZS output start Proof for theBenchmark
% 2.76/0.74  fof(f2452,plain,(
% 2.76/0.74    $false),
% 2.76/0.74    inference(avatar_sat_refutation,[],[f110,f116,f252,f255,f256,f587,f659,f1094,f1096,f2305,f2352,f2361,f2451])).
% 2.76/0.74  fof(f2451,plain,(
% 2.76/0.74    spl9_17 | ~spl9_13 | ~spl9_15),
% 2.76/0.74    inference(avatar_split_clause,[],[f2442,f249,f217,f276])).
% 2.76/0.74  fof(f276,plain,(
% 2.76/0.74    spl9_17 <=> r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK1))),
% 2.76/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_17])])).
% 2.76/0.74  fof(f217,plain,(
% 2.76/0.74    spl9_13 <=> r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK1)),
% 2.76/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_13])])).
% 2.76/0.74  fof(f249,plain,(
% 2.76/0.74    spl9_15 <=> ! [X0] : (~r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),X0) | r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,X0)))),
% 2.76/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 2.76/0.74  fof(f2442,plain,(
% 2.76/0.74    r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK1)) | (~spl9_13 | ~spl9_15)),
% 2.76/0.74    inference(resolution,[],[f250,f219])).
% 2.76/0.74  fof(f219,plain,(
% 2.76/0.74    r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK1) | ~spl9_13),
% 2.76/0.74    inference(avatar_component_clause,[],[f217])).
% 2.76/0.74  fof(f250,plain,(
% 2.76/0.74    ( ! [X0] : (~r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),X0) | r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,X0))) ) | ~spl9_15),
% 2.76/0.74    inference(avatar_component_clause,[],[f249])).
% 2.76/0.74  fof(f2361,plain,(
% 2.76/0.74    spl9_12 | spl9_13 | ~spl9_4),
% 2.76/0.74    inference(avatar_split_clause,[],[f206,f107,f217,f213])).
% 2.76/0.74  fof(f213,plain,(
% 2.76/0.74    spl9_12 <=> r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK0)),
% 2.76/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 2.76/0.74  fof(f107,plain,(
% 2.76/0.74    spl9_4 <=> r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),
% 2.76/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 2.76/0.74  fof(f206,plain,(
% 2.76/0.74    r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK1) | r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK0) | ~spl9_4),
% 2.76/0.74    inference(resolution,[],[f109,f58])).
% 2.76/0.74  fof(f58,plain,(
% 2.76/0.74    ( ! [X4,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 2.76/0.74    inference(equality_resolution,[],[f52])).
% 2.76/0.74  fof(f52,plain,(
% 2.76/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2) )),
% 2.76/0.74    inference(definition_unfolding,[],[f40,f35])).
% 2.76/0.74  fof(f35,plain,(
% 2.76/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.76/0.74    inference(cnf_transformation,[],[f2])).
% 2.76/0.74  fof(f2,axiom,(
% 2.76/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.76/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.76/0.74  fof(f40,plain,(
% 2.76/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.76/0.74    inference(cnf_transformation,[],[f26])).
% 2.76/0.74  fof(f26,plain,(
% 2.76/0.74    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | (((~r2_hidden(sK7(X0,X1,X2),X1) & ~r2_hidden(sK7(X0,X1,X2),X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.76/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f24,f25])).
% 2.76/0.74  fof(f25,plain,(
% 2.76/0.74    ! [X2,X1,X0] : (? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2))) => (((~r2_hidden(sK7(X0,X1,X2),X1) & ~r2_hidden(sK7(X0,X1,X2),X0)) | ~r2_hidden(sK7(X0,X1,X2),X2)) & (r2_hidden(sK7(X0,X1,X2),X1) | r2_hidden(sK7(X0,X1,X2),X0) | r2_hidden(sK7(X0,X1,X2),X2))))),
% 2.76/0.74    introduced(choice_axiom,[])).
% 2.76/0.74  fof(f24,plain,(
% 2.76/0.74    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (~r2_hidden(X4,X1) & ~r2_hidden(X4,X0))) & (r2_hidden(X4,X1) | r2_hidden(X4,X0) | ~r2_hidden(X4,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.76/0.74    inference(rectify,[],[f23])).
% 2.76/0.74  fof(f23,plain,(
% 2.76/0.74    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & (r2_hidden(X3,X1) | r2_hidden(X3,X0) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.76/0.74    inference(flattening,[],[f22])).
% 2.76/0.74  fof(f22,plain,(
% 2.76/0.74    ! [X0,X1,X2] : ((k2_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) & ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) & ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) | r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k2_xboole_0(X0,X1) != X2))),
% 2.76/0.74    inference(nnf_transformation,[],[f1])).
% 2.76/0.74  fof(f1,axiom,(
% 2.76/0.74    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.76/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.76/0.74  fof(f109,plain,(
% 2.76/0.74    r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) | ~spl9_4),
% 2.76/0.74    inference(avatar_component_clause,[],[f107])).
% 2.76/0.74  fof(f2352,plain,(
% 2.76/0.74    ~spl9_17 | ~spl9_5 | ~spl9_17),
% 2.76/0.74    inference(avatar_split_clause,[],[f2347,f276,f112,f276])).
% 2.76/0.74  fof(f112,plain,(
% 2.76/0.74    spl9_5 <=> ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) | ~r2_hidden(k4_tarski(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),X0),sK2))),
% 2.76/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 2.76/0.74  fof(f2347,plain,(
% 2.76/0.74    ~r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK1)) | (~spl9_5 | ~spl9_17)),
% 2.76/0.74    inference(resolution,[],[f1064,f79])).
% 2.76/0.74  fof(f79,plain,(
% 2.76/0.74    ( ! [X4,X5,X3] : (r2_hidden(sK6(X3,X4,sK2),k5_xboole_0(X5,k4_xboole_0(X4,X5))) | ~r2_hidden(X3,k10_relat_1(sK2,X4))) )),
% 2.76/0.74    inference(resolution,[],[f70,f56])).
% 2.76/0.74  fof(f56,plain,(
% 2.76/0.74    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | ~r2_hidden(X4,X1)) )),
% 2.76/0.74    inference(equality_resolution,[],[f50])).
% 2.76/0.74  fof(f50,plain,(
% 2.76/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2) )),
% 2.76/0.74    inference(definition_unfolding,[],[f42,f35])).
% 2.76/0.74  fof(f42,plain,(
% 2.76/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | k2_xboole_0(X0,X1) != X2) )),
% 2.76/0.74    inference(cnf_transformation,[],[f26])).
% 2.76/0.74  fof(f70,plain,(
% 2.76/0.74    ( ! [X4,X5] : (r2_hidden(sK6(X4,X5,sK2),X5) | ~r2_hidden(X4,k10_relat_1(sK2,X5))) )),
% 2.76/0.74    inference(resolution,[],[f27,f38])).
% 2.76/0.74  fof(f38,plain,(
% 2.76/0.74    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X1) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.76/0.74    inference(cnf_transformation,[],[f21])).
% 2.76/0.74  fof(f21,plain,(
% 2.76/0.74    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & ((r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.76/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f19,f20])).
% 2.76/0.74  fof(f20,plain,(
% 2.76/0.74    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) => (r2_hidden(sK6(X0,X1,X2),X1) & r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) & r2_hidden(sK6(X0,X1,X2),k2_relat_1(X2))))),
% 2.76/0.74    introduced(choice_axiom,[])).
% 2.76/0.74  fof(f19,plain,(
% 2.76/0.74    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X0,X4),X2) & r2_hidden(X4,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.76/0.74    inference(rectify,[],[f18])).
% 2.76/0.74  fof(f18,plain,(
% 2.76/0.74    ! [X0,X1,X2] : (((r2_hidden(X0,k10_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,k2_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2))) | ~r2_hidden(X0,k10_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 2.76/0.74    inference(nnf_transformation,[],[f9])).
% 2.76/0.74  fof(f9,plain,(
% 2.76/0.74    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 2.76/0.74    inference(ennf_transformation,[],[f4])).
% 2.76/0.74  fof(f4,axiom,(
% 2.76/0.74    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 2.76/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).
% 2.76/0.74  fof(f27,plain,(
% 2.76/0.74    v1_relat_1(sK2)),
% 2.76/0.74    inference(cnf_transformation,[],[f11])).
% 2.76/0.74  fof(f11,plain,(
% 2.76/0.74    k10_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_relat_1(sK2)),
% 2.76/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).
% 2.76/0.74  fof(f10,plain,(
% 2.76/0.74    ? [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_relat_1(X2)) => (k10_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_relat_1(sK2))),
% 2.76/0.74    introduced(choice_axiom,[])).
% 2.76/0.74  fof(f7,plain,(
% 2.76/0.74    ? [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) != k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_relat_1(X2))),
% 2.76/0.74    inference(ennf_transformation,[],[f6])).
% 2.76/0.74  fof(f6,negated_conjecture,(
% 2.76/0.74    ~! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.76/0.74    inference(negated_conjecture,[],[f5])).
% 2.76/0.74  fof(f5,conjecture,(
% 2.76/0.74    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 2.76/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).
% 2.76/0.74  fof(f1064,plain,(
% 2.76/0.74    ~r2_hidden(sK6(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK1,sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) | (~spl9_5 | ~spl9_17)),
% 2.76/0.74    inference(resolution,[],[f257,f278])).
% 2.76/0.74  fof(f278,plain,(
% 2.76/0.74    r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK1)) | ~spl9_17),
% 2.76/0.74    inference(avatar_component_clause,[],[f276])).
% 2.76/0.74  fof(f257,plain,(
% 2.76/0.74    ( ! [X0] : (~r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,X0)) | ~r2_hidden(sK6(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),X0,sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ) | ~spl9_5),
% 2.76/0.74    inference(resolution,[],[f113,f69])).
% 2.76/0.74  fof(f69,plain,(
% 2.76/0.74    ( ! [X2,X3] : (r2_hidden(k4_tarski(X2,sK6(X2,X3,sK2)),sK2) | ~r2_hidden(X2,k10_relat_1(sK2,X3))) )),
% 2.76/0.74    inference(resolution,[],[f27,f37])).
% 2.76/0.74  fof(f37,plain,(
% 2.76/0.74    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,sK6(X0,X1,X2)),X2) | ~r2_hidden(X0,k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 2.76/0.74    inference(cnf_transformation,[],[f21])).
% 2.76/0.74  fof(f113,plain,(
% 2.76/0.74    ( ! [X0] : (~r2_hidden(k4_tarski(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),X0),sK2) | ~r2_hidden(X0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ) | ~spl9_5),
% 2.76/0.74    inference(avatar_component_clause,[],[f112])).
% 2.76/0.74  fof(f2305,plain,(
% 2.76/0.74    ~spl9_16 | ~spl9_5 | ~spl9_16),
% 2.76/0.74    inference(avatar_split_clause,[],[f2300,f272,f112,f272])).
% 2.76/0.74  fof(f272,plain,(
% 2.76/0.74    spl9_16 <=> r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK0))),
% 2.76/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 2.76/0.74  fof(f2300,plain,(
% 2.76/0.74    ~r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK0)) | (~spl9_5 | ~spl9_16)),
% 2.76/0.74    inference(resolution,[],[f1063,f78])).
% 2.76/0.74  fof(f78,plain,(
% 2.76/0.74    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,sK2),k5_xboole_0(X1,k4_xboole_0(X2,X1))) | ~r2_hidden(X0,k10_relat_1(sK2,X1))) )),
% 2.76/0.74    inference(resolution,[],[f70,f57])).
% 2.76/0.74  fof(f57,plain,(
% 2.76/0.74    ( ! [X4,X0,X1] : (r2_hidden(X4,k5_xboole_0(X0,k4_xboole_0(X1,X0))) | ~r2_hidden(X4,X0)) )),
% 2.76/0.74    inference(equality_resolution,[],[f51])).
% 2.76/0.74  fof(f51,plain,(
% 2.76/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k5_xboole_0(X0,k4_xboole_0(X1,X0)) != X2) )),
% 2.76/0.74    inference(definition_unfolding,[],[f41,f35])).
% 2.76/0.74  fof(f41,plain,(
% 2.76/0.74    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X0) | k2_xboole_0(X0,X1) != X2) )),
% 2.76/0.74    inference(cnf_transformation,[],[f26])).
% 2.76/0.74  fof(f1063,plain,(
% 2.76/0.74    ~r2_hidden(sK6(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK0,sK2),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) | (~spl9_5 | ~spl9_16)),
% 2.76/0.74    inference(resolution,[],[f257,f274])).
% 2.76/0.74  fof(f274,plain,(
% 2.76/0.74    r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK0)) | ~spl9_16),
% 2.76/0.74    inference(avatar_component_clause,[],[f272])).
% 2.76/0.74  fof(f1096,plain,(
% 2.76/0.74    ~spl9_17 | spl9_2),
% 2.76/0.74    inference(avatar_split_clause,[],[f224,f98,f276])).
% 2.76/0.74  fof(f98,plain,(
% 2.76/0.74    spl9_2 <=> r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))))),
% 2.76/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 2.76/0.74  fof(f224,plain,(
% 2.76/0.74    ~r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK1)) | spl9_2),
% 2.76/0.74    inference(resolution,[],[f99,f56])).
% 2.76/0.74  fof(f99,plain,(
% 2.76/0.74    ~r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))) | spl9_2),
% 2.76/0.74    inference(avatar_component_clause,[],[f98])).
% 2.76/0.74  fof(f1094,plain,(
% 2.76/0.74    spl9_16 | ~spl9_12 | ~spl9_15),
% 2.76/0.74    inference(avatar_split_clause,[],[f991,f249,f213,f272])).
% 2.76/0.74  fof(f991,plain,(
% 2.76/0.74    r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK0)) | (~spl9_12 | ~spl9_15)),
% 2.76/0.74    inference(resolution,[],[f250,f215])).
% 2.76/0.74  fof(f215,plain,(
% 2.76/0.74    r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK0) | ~spl9_12),
% 2.76/0.74    inference(avatar_component_clause,[],[f213])).
% 2.76/0.74  fof(f659,plain,(
% 2.76/0.74    spl9_16 | spl9_17 | ~spl9_2),
% 2.76/0.74    inference(avatar_split_clause,[],[f265,f98,f276,f272])).
% 2.76/0.74  fof(f265,plain,(
% 2.76/0.74    r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK1)) | r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK0)) | ~spl9_2),
% 2.76/0.74    inference(resolution,[],[f100,f58])).
% 2.76/0.74  fof(f100,plain,(
% 2.76/0.74    r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))) | ~spl9_2),
% 2.76/0.74    inference(avatar_component_clause,[],[f98])).
% 2.76/0.74  fof(f587,plain,(
% 2.76/0.74    ~spl9_16 | spl9_2),
% 2.76/0.74    inference(avatar_split_clause,[],[f223,f98,f272])).
% 2.76/0.74  fof(f223,plain,(
% 2.76/0.74    ~r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,sK0)) | spl9_2),
% 2.76/0.74    inference(resolution,[],[f99,f57])).
% 2.76/0.74  fof(f256,plain,(
% 2.76/0.74    spl9_2 | spl9_3),
% 2.76/0.74    inference(avatar_split_clause,[],[f205,f102,f98])).
% 2.76/0.74  fof(f102,plain,(
% 2.76/0.74    spl9_3 <=> r2_hidden(k4_tarski(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))))),sK2)),
% 2.76/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 2.76/0.74  fof(f205,plain,(
% 2.76/0.74    r2_hidden(k4_tarski(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))))),sK2) | r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))))),
% 2.76/0.74    inference(resolution,[],[f77,f60])).
% 2.76/0.74  fof(f60,plain,(
% 2.76/0.74    ~sQ8_eqProxy(k10_relat_1(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))))),
% 2.76/0.74    inference(equality_proxy_replacement,[],[f46,f59])).
% 2.76/0.74  fof(f59,plain,(
% 2.76/0.74    ! [X1,X0] : (sQ8_eqProxy(X0,X1) <=> X0 = X1)),
% 2.76/0.74    introduced(equality_proxy_definition,[new_symbols(naming,[sQ8_eqProxy])])).
% 2.76/0.74  fof(f46,plain,(
% 2.76/0.74    k10_relat_1(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) != k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),
% 2.76/0.74    inference(definition_unfolding,[],[f28,f35,f35])).
% 2.76/0.74  fof(f28,plain,(
% 2.76/0.74    k10_relat_1(sK2,k2_xboole_0(sK0,sK1)) != k2_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 2.76/0.74    inference(cnf_transformation,[],[f11])).
% 2.76/0.74  fof(f77,plain,(
% 2.76/0.74    ( ! [X21,X22] : (sQ8_eqProxy(k10_relat_1(sK2,X21),X22) | r2_hidden(k4_tarski(sK3(sK2,X21,X22),sK4(sK2,X21,X22)),sK2) | r2_hidden(sK3(sK2,X21,X22),X22)) )),
% 2.76/0.74    inference(resolution,[],[f27,f63])).
% 2.76/0.74  fof(f63,plain,(
% 2.76/0.74    ( ! [X2,X0,X1] : (sQ8_eqProxy(k10_relat_1(X0,X1),X2) | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(sK3(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 2.76/0.74    inference(equality_proxy_replacement,[],[f32,f59])).
% 2.76/0.74  fof(f32,plain,(
% 2.76/0.74    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0) | r2_hidden(sK3(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 2.76/0.74    inference(cnf_transformation,[],[f17])).
% 2.76/0.74  fof(f17,plain,(
% 2.76/0.74    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & ((r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.76/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f13,f16,f15,f14])).
% 2.76/0.74  fof(f14,plain,(
% 2.76/0.74    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0)) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.76/0.74    introduced(choice_axiom,[])).
% 2.76/0.74  fof(f15,plain,(
% 2.76/0.74    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X5),X0)) => (r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),sK4(X0,X1,X2)),X0)))),
% 2.76/0.74    introduced(choice_axiom,[])).
% 2.76/0.74  fof(f16,plain,(
% 2.76/0.74    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) => (r2_hidden(sK5(X0,X1,X6),X1) & r2_hidden(k4_tarski(X6,sK5(X0,X1,X6)),X0)))),
% 2.76/0.74    introduced(choice_axiom,[])).
% 2.76/0.74  fof(f13,plain,(
% 2.76/0.74    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X3,X5),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X6,X8),X0)) | ~r2_hidden(X6,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.76/0.74    inference(rectify,[],[f12])).
% 2.76/0.74  fof(f12,plain,(
% 2.76/0.74    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X3,X4),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 2.76/0.74    inference(nnf_transformation,[],[f8])).
% 2.76/0.74  fof(f8,plain,(
% 2.76/0.74    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 2.76/0.74    inference(ennf_transformation,[],[f3])).
% 2.76/0.74  fof(f3,axiom,(
% 2.76/0.74    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 2.76/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d14_relat_1)).
% 2.76/0.74  fof(f255,plain,(
% 2.76/0.74    ~spl9_2 | spl9_5),
% 2.76/0.74    inference(avatar_split_clause,[],[f197,f112,f98])).
% 2.76/0.74  fof(f197,plain,(
% 2.76/0.74    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) | ~r2_hidden(k4_tarski(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),X0),sK2) | ~r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))))) )),
% 2.76/0.74    inference(resolution,[],[f75,f60])).
% 2.76/0.74  fof(f75,plain,(
% 2.76/0.74    ( ! [X17,X18,X16] : (sQ8_eqProxy(k10_relat_1(sK2,X16),X17) | ~r2_hidden(X18,X16) | ~r2_hidden(k4_tarski(sK3(sK2,X16,X17),X18),sK2) | ~r2_hidden(sK3(sK2,X16,X17),X17)) )),
% 2.76/0.74    inference(resolution,[],[f27,f61])).
% 2.76/0.74  fof(f61,plain,(
% 2.76/0.74    ( ! [X4,X2,X0,X1] : (sQ8_eqProxy(k10_relat_1(X0,X1),X2) | ~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 2.76/0.74    inference(equality_proxy_replacement,[],[f34,f59])).
% 2.76/0.74  fof(f34,plain,(
% 2.76/0.74    ( ! [X4,X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | ~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(sK3(X0,X1,X2),X4),X0) | ~r2_hidden(sK3(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 2.76/0.74    inference(cnf_transformation,[],[f17])).
% 2.76/0.74  fof(f252,plain,(
% 2.76/0.74    spl9_15 | ~spl9_3),
% 2.76/0.74    inference(avatar_split_clause,[],[f235,f102,f249])).
% 2.76/0.74  fof(f235,plain,(
% 2.76/0.74    ( ! [X1] : (~r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),X1) | r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k10_relat_1(sK2,X1))) ) | ~spl9_3),
% 2.76/0.74    inference(resolution,[],[f104,f72])).
% 2.76/0.74  fof(f72,plain,(
% 2.76/0.74    ( ! [X10,X11,X9] : (~r2_hidden(k4_tarski(X9,X11),sK2) | ~r2_hidden(X11,X10) | r2_hidden(X9,k10_relat_1(sK2,X10))) )),
% 2.76/0.74    inference(resolution,[],[f27,f53])).
% 2.76/0.74  fof(f53,plain,(
% 2.76/0.74    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k10_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | ~v1_relat_1(X0)) )),
% 2.76/0.74    inference(equality_resolution,[],[f31])).
% 2.76/0.74  fof(f31,plain,(
% 2.76/0.74    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X6,X7),X0) | k10_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 2.76/0.74    inference(cnf_transformation,[],[f17])).
% 2.76/0.74  fof(f104,plain,(
% 2.76/0.74    r2_hidden(k4_tarski(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0))))),sK2) | ~spl9_3),
% 2.76/0.74    inference(avatar_component_clause,[],[f102])).
% 2.76/0.74  fof(f116,plain,(
% 2.76/0.74    spl9_1),
% 2.76/0.74    inference(avatar_contradiction_clause,[],[f115])).
% 2.76/0.74  fof(f115,plain,(
% 2.76/0.74    $false | spl9_1),
% 2.76/0.74    inference(resolution,[],[f96,f27])).
% 2.76/0.74  fof(f96,plain,(
% 2.76/0.74    ~v1_relat_1(sK2) | spl9_1),
% 2.76/0.74    inference(avatar_component_clause,[],[f94])).
% 2.76/0.74  fof(f94,plain,(
% 2.76/0.74    spl9_1 <=> v1_relat_1(sK2)),
% 2.76/0.74    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 2.76/0.74  fof(f110,plain,(
% 2.76/0.74    ~spl9_1 | spl9_2 | spl9_4),
% 2.76/0.74    inference(avatar_split_clause,[],[f91,f107,f98,f94])).
% 2.76/0.74  fof(f91,plain,(
% 2.76/0.74    r2_hidden(sK4(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) | r2_hidden(sK3(sK2,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))),k5_xboole_0(k10_relat_1(sK2,sK0),k4_xboole_0(k10_relat_1(sK2,sK1),k10_relat_1(sK2,sK0)))) | ~v1_relat_1(sK2)),
% 2.76/0.74    inference(resolution,[],[f60,f62])).
% 2.76/0.74  fof(f62,plain,(
% 2.76/0.74    ( ! [X2,X0,X1] : (sQ8_eqProxy(k10_relat_1(X0,X1),X2) | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 2.76/0.74    inference(equality_proxy_replacement,[],[f33,f59])).
% 2.76/0.74  fof(f33,plain,(
% 2.76/0.74    ( ! [X2,X0,X1] : (k10_relat_1(X0,X1) = X2 | r2_hidden(sK4(X0,X1,X2),X1) | r2_hidden(sK3(X0,X1,X2),X2) | ~v1_relat_1(X0)) )),
% 2.76/0.74    inference(cnf_transformation,[],[f17])).
% 2.76/0.74  % SZS output end Proof for theBenchmark
% 2.76/0.74  % (2150)------------------------------
% 2.76/0.74  % (2150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.76/0.74  % (2150)Termination reason: Refutation
% 2.76/0.74  
% 2.76/0.74  % (2150)Memory used [KB]: 8315
% 2.76/0.74  % (2150)Time elapsed: 0.264 s
% 2.76/0.74  % (2150)------------------------------
% 2.76/0.74  % (2150)------------------------------
% 2.76/0.75  % (2134)Success in time 0.376 s
%------------------------------------------------------------------------------

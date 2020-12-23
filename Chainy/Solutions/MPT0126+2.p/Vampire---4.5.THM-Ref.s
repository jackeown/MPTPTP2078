%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0126+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:11 EST 2020

% Result     : Theorem 18.65s
% Output     : Refutation 18.65s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 237 expanded)
%              Number of leaves         :   32 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  550 (1388 expanded)
%              Number of equality atoms :  224 ( 646 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36794,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f631,f5676,f5987,f23583,f28235,f28330,f28476,f28611,f28631,f28985,f29105,f29243,f29306,f32860,f33597,f33693,f36684,f36685,f36709])).

fof(f36709,plain,(
    spl22_5535 ),
    inference(avatar_contradiction_clause,[],[f36691])).

fof(f36691,plain,
    ( $false
    | spl22_5535 ),
    inference(resolution,[],[f36642,f611])).

fof(f611,plain,(
    ! [X2,X5,X1] : r2_hidden(X5,k1_enumset1(X5,X1,X2)) ),
    inference(equality_resolution,[],[f610])).

fof(f610,plain,(
    ! [X2,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X5,X1,X2) != X3 ) ),
    inference(equality_resolution,[],[f418])).

fof(f418,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X0 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f311])).

fof(f311,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ( ( ( sK6(X0,X1,X2,X3) != X2
              & sK6(X0,X1,X2,X3) != X1
              & sK6(X0,X1,X2,X3) != X0 )
            | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
          & ( sK6(X0,X1,X2,X3) = X2
            | sK6(X0,X1,X2,X3) = X1
            | sK6(X0,X1,X2,X3) = X0
            | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f309,f310])).

fof(f310,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X2 != X4
              & X1 != X4
              & X0 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X2 = X4
            | X1 = X4
            | X0 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK6(X0,X1,X2,X3) != X2
            & sK6(X0,X1,X2,X3) != X1
            & sK6(X0,X1,X2,X3) != X0 )
          | ~ r2_hidden(sK6(X0,X1,X2,X3),X3) )
        & ( sK6(X0,X1,X2,X3) = X2
          | sK6(X0,X1,X2,X3) = X1
          | sK6(X0,X1,X2,X3) = X0
          | r2_hidden(sK6(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f309,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X2 != X5
                & X1 != X5
                & X0 != X5 ) )
            & ( X2 = X5
              | X1 = X5
              | X0 = X5
              | ~ r2_hidden(X5,X3) ) )
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(rectify,[],[f308])).

fof(f308,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(flattening,[],[f307])).

fof(f307,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
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
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f204])).

fof(f204,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f174])).

fof(f174,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f36642,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))
    | spl22_5535 ),
    inference(avatar_component_clause,[],[f36641])).

fof(f36641,plain,
    ( spl22_5535
  <=> r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_5535])])).

fof(f36685,plain,
    ( sK0 != sK13(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ r2_hidden(sK13(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0))
    | r2_hidden(sK0,k1_tarski(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f36684,plain,
    ( ~ spl22_5545
    | spl22_1
    | ~ spl22_5535
    | ~ spl22_4665 ),
    inference(avatar_split_clause,[],[f36637,f28734,f36641,f629,f36681])).

fof(f36681,plain,
    ( spl22_5545
  <=> r2_hidden(sK0,k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_5545])])).

fof(f629,plain,
    ( spl22_1
  <=> k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_1])])).

fof(f28734,plain,
    ( spl22_4665
  <=> sK0 = sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_4665])])).

fof(f36637,plain,
    ( ~ r2_hidden(sK0,k1_enumset1(sK0,sK1,sK2))
    | k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ r2_hidden(sK0,k1_tarski(sK0))
    | ~ spl22_4665 ),
    inference(superposition,[],[f489,f28735])).

fof(f28735,plain,
    ( sK0 = sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | ~ spl22_4665 ),
    inference(avatar_component_clause,[],[f28734])).

fof(f489,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK8(X0,X1,X2),X0)
      | ~ r2_hidden(sK8(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f322])).

fof(f322,plain,(
    ! [X0,X1,X2] :
      ( ( k2_xboole_0(X0,X1) = X2
        | ( ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
              & ~ r2_hidden(sK8(X0,X1,X2),X0) )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( r2_hidden(sK8(X0,X1,X2),X1)
            | r2_hidden(sK8(X0,X1,X2),X0)
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( ~ r2_hidden(X4,X1)
                & ~ r2_hidden(X4,X0) ) )
            & ( r2_hidden(X4,X1)
              | r2_hidden(X4,X0)
              | ~ r2_hidden(X4,X2) ) )
        | k2_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f320,f321])).

fof(f321,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( ~ r2_hidden(X3,X1)
              & ~ r2_hidden(X3,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0)
            | r2_hidden(X3,X2) ) )
     => ( ( ( ~ r2_hidden(sK8(X0,X1,X2),X1)
            & ~ r2_hidden(sK8(X0,X1,X2),X0) )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( r2_hidden(sK8(X0,X1,X2),X1)
          | r2_hidden(sK8(X0,X1,X2),X0)
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f320,plain,(
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
    inference(rectify,[],[f319])).

fof(f319,plain,(
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
    inference(flattening,[],[f318])).

fof(f318,plain,(
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
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f33693,plain,
    ( spl22_4665
    | ~ spl22_143 ),
    inference(avatar_split_clause,[],[f33663,f1363,f28734])).

fof(f1363,plain,
    ( spl22_143
  <=> r2_hidden(sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_143])])).

fof(f33663,plain,
    ( sK0 = sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | ~ spl22_143 ),
    inference(resolution,[],[f1543,f605])).

fof(f605,plain,(
    ! [X0,X3] :
      ( X0 = X3
      | ~ r2_hidden(X3,k1_tarski(X0)) ) ),
    inference(equality_resolution,[],[f413])).

fof(f413,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f306])).

fof(f306,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f304,f305])).

fof(f305,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f304,plain,(
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
    inference(rectify,[],[f303])).

fof(f303,plain,(
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
    inference(nnf_transformation,[],[f175])).

fof(f175,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1543,plain,
    ( r2_hidden(sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_tarski(sK0))
    | ~ spl22_143 ),
    inference(avatar_component_clause,[],[f1363])).

fof(f33597,plain,(
    spl22_4608 ),
    inference(avatar_contradiction_clause,[],[f33580])).

fof(f33580,plain,
    ( $false
    | spl22_4608 ),
    inference(resolution,[],[f28233,f599])).

fof(f599,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f598])).

fof(f598,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f407])).

fof(f407,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f302])).

fof(f302,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK4(X0,X1,X2) != X1
              & sK4(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( sK4(X0,X1,X2) = X1
            | sK4(X0,X1,X2) = X0
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f300,f301])).

fof(f301,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK4(X0,X1,X2) != X1
            & sK4(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( sK4(X0,X1,X2) = X1
          | sK4(X0,X1,X2) = X0
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f300,plain,(
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
    inference(rectify,[],[f299])).

fof(f299,plain,(
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
    inference(flattening,[],[f298])).

fof(f298,plain,(
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
    inference(nnf_transformation,[],[f176])).

fof(f176,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f28233,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | spl22_4608 ),
    inference(avatar_component_clause,[],[f28232])).

fof(f28232,plain,
    ( spl22_4608
  <=> r2_hidden(sK2,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_4608])])).

fof(f32860,plain,(
    spl22_4647 ),
    inference(avatar_contradiction_clause,[],[f32843])).

fof(f32843,plain,
    ( $false
    | spl22_4647 ),
    inference(resolution,[],[f28609,f601])).

fof(f601,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f600])).

fof(f600,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f406])).

fof(f406,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f302])).

fof(f28609,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | spl22_4647 ),
    inference(avatar_component_clause,[],[f28608])).

fof(f28608,plain,
    ( spl22_4647
  <=> r2_hidden(sK1,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_4647])])).

fof(f29306,plain,
    ( spl22_3686
    | spl22_3668 ),
    inference(avatar_split_clause,[],[f29290,f22372,f22469])).

fof(f22469,plain,
    ( spl22_3686
  <=> ! [X6] :
        ( ~ r2_hidden(sK0,X6)
        | ~ r1_tarski(X6,k2_tarski(sK1,sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_3686])])).

fof(f22372,plain,
    ( spl22_3668
  <=> r2_hidden(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_3668])])).

fof(f29290,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK0,X6)
        | ~ r1_tarski(X6,k2_tarski(sK1,sK2)) )
    | spl22_3668 ),
    inference(resolution,[],[f22373,f510])).

fof(f510,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f341])).

fof(f341,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK13(X0,X1),X1)
          & r2_hidden(sK13(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f339,f340])).

fof(f340,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK13(X0,X1),X1)
        & r2_hidden(sK13(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f339,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f338])).

fof(f338,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f248])).

fof(f248,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f22373,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK1,sK2))
    | spl22_3668 ),
    inference(avatar_component_clause,[],[f22372])).

fof(f29243,plain,
    ( sK0 != sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | ~ r2_hidden(sK0,k2_tarski(sK1,sK2))
    | r2_hidden(sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k2_tarski(sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f29105,plain,
    ( spl22_4665
    | spl22_274
    | spl22_275
    | ~ spl22_142 ),
    inference(avatar_split_clause,[],[f29076,f1360,f2125,f2122,f28734])).

fof(f2122,plain,
    ( spl22_274
  <=> sK1 = sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_274])])).

fof(f2125,plain,
    ( spl22_275
  <=> sK2 = sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_275])])).

fof(f1360,plain,
    ( spl22_142
  <=> r2_hidden(sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_142])])).

fof(f29076,plain,
    ( sK2 = sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | sK0 = sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | ~ spl22_142 ),
    inference(resolution,[],[f1542,f612])).

fof(f612,plain,(
    ! [X2,X0,X5,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,k1_enumset1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f417])).

fof(f417,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( X2 = X5
      | X1 = X5
      | X0 = X5
      | ~ r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f311])).

fof(f1542,plain,
    ( r2_hidden(sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | ~ spl22_142 ),
    inference(avatar_component_clause,[],[f1360])).

fof(f28985,plain,
    ( spl22_142
    | spl22_143
    | spl22_1
    | spl22_169 ),
    inference(avatar_split_clause,[],[f28962,f1497,f629,f1363,f1360])).

fof(f1497,plain,
    ( spl22_169
  <=> r2_hidden(sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_169])])).

fof(f28962,plain,
    ( k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | r2_hidden(sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_tarski(sK0))
    | r2_hidden(sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k1_enumset1(sK0,sK1,sK2))
    | spl22_169 ),
    inference(resolution,[],[f1498,f488])).

fof(f488,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | r2_hidden(sK8(X0,X1,X2),X1)
      | r2_hidden(sK8(X0,X1,X2),X0)
      | r2_hidden(sK8(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f322])).

fof(f1498,plain,
    ( ~ r2_hidden(sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k2_tarski(sK1,sK2))
    | spl22_169 ),
    inference(avatar_component_clause,[],[f1497])).

fof(f28631,plain,(
    spl22_4637 ),
    inference(avatar_contradiction_clause,[],[f28613])).

fof(f28613,plain,
    ( $false
    | spl22_4637 ),
    inference(resolution,[],[f28569,f609])).

fof(f609,plain,(
    ! [X2,X0,X5] : r2_hidden(X5,k1_enumset1(X0,X5,X2)) ),
    inference(equality_resolution,[],[f608])).

fof(f608,plain,(
    ! [X2,X0,X5,X3] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X5,X2) != X3 ) ),
    inference(equality_resolution,[],[f419])).

fof(f419,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X1 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f311])).

fof(f28569,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2))
    | spl22_4637 ),
    inference(avatar_component_clause,[],[f28568])).

fof(f28568,plain,
    ( spl22_4637
  <=> r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_4637])])).

fof(f28611,plain,
    ( ~ spl22_4647
    | spl22_1
    | ~ spl22_4637
    | ~ spl22_274 ),
    inference(avatar_split_clause,[],[f28566,f2122,f28568,f629,f28608])).

fof(f28566,plain,
    ( ~ r2_hidden(sK1,k1_enumset1(sK0,sK1,sK2))
    | k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK2))
    | ~ spl22_274 ),
    inference(superposition,[],[f490,f2123])).

fof(f2123,plain,
    ( sK1 = sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | ~ spl22_274 ),
    inference(avatar_component_clause,[],[f2122])).

fof(f490,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK8(X0,X1,X2),X1)
      | ~ r2_hidden(sK8(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f322])).

fof(f28476,plain,
    ( spl22_274
    | spl22_275
    | ~ spl22_169 ),
    inference(avatar_split_clause,[],[f28446,f1497,f2125,f2122])).

fof(f28446,plain,
    ( sK2 = sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | sK1 = sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | ~ spl22_169 ),
    inference(resolution,[],[f1544,f602])).

fof(f602,plain,(
    ! [X4,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,k2_tarski(X0,X1)) ) ),
    inference(equality_resolution,[],[f405])).

fof(f405,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f302])).

fof(f1544,plain,
    ( r2_hidden(sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2)),k2_tarski(sK1,sK2))
    | ~ spl22_169 ),
    inference(avatar_component_clause,[],[f1497])).

fof(f28330,plain,(
    spl22_4598 ),
    inference(avatar_contradiction_clause,[],[f28312])).

fof(f28312,plain,
    ( $false
    | spl22_4598 ),
    inference(resolution,[],[f28193,f607])).

fof(f607,plain,(
    ! [X0,X5,X1] : r2_hidden(X5,k1_enumset1(X0,X1,X5)) ),
    inference(equality_resolution,[],[f606])).

fof(f606,plain,(
    ! [X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | k1_enumset1(X0,X1,X5) != X3 ) ),
    inference(equality_resolution,[],[f420])).

fof(f420,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f311])).

fof(f28193,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2))
    | spl22_4598 ),
    inference(avatar_component_clause,[],[f28192])).

fof(f28192,plain,
    ( spl22_4598
  <=> r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_4598])])).

fof(f28235,plain,
    ( ~ spl22_4608
    | spl22_1
    | ~ spl22_4598
    | ~ spl22_275 ),
    inference(avatar_split_clause,[],[f28190,f2125,f28192,f629,f28232])).

fof(f28190,plain,
    ( ~ r2_hidden(sK2,k1_enumset1(sK0,sK1,sK2))
    | k1_enumset1(sK0,sK1,sK2) = k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ r2_hidden(sK2,k2_tarski(sK1,sK2))
    | ~ spl22_275 ),
    inference(superposition,[],[f490,f2126])).

fof(f2126,plain,
    ( sK2 = sK8(k1_tarski(sK0),k2_tarski(sK1,sK2),k1_enumset1(sK0,sK1,sK2))
    | ~ spl22_275 ),
    inference(avatar_component_clause,[],[f2125])).

fof(f23583,plain,
    ( ~ spl22_10
    | ~ spl22_3686 ),
    inference(avatar_split_clause,[],[f23492,f22469,f677])).

fof(f677,plain,
    ( spl22_10
  <=> r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_10])])).

fof(f23492,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl22_3686 ),
    inference(resolution,[],[f22470,f604])).

fof(f604,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f603])).

fof(f603,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f414])).

fof(f414,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f306])).

fof(f22470,plain,
    ( ! [X6] :
        ( ~ r2_hidden(sK0,X6)
        | ~ r1_tarski(X6,k2_tarski(sK1,sK2)) )
    | ~ spl22_3686 ),
    inference(avatar_component_clause,[],[f22469])).

fof(f5987,plain,
    ( spl22_906
    | ~ spl22_20 ),
    inference(avatar_split_clause,[],[f5959,f731,f5985])).

fof(f5985,plain,
    ( spl22_906
  <=> sK0 = sK13(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_906])])).

fof(f731,plain,
    ( spl22_20
  <=> r2_hidden(sK13(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_20])])).

fof(f5959,plain,
    ( sK0 = sK13(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | ~ spl22_20 ),
    inference(resolution,[],[f732,f605])).

fof(f732,plain,
    ( r2_hidden(sK13(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0))
    | ~ spl22_20 ),
    inference(avatar_component_clause,[],[f731])).

fof(f5676,plain,
    ( spl22_20
    | spl22_10 ),
    inference(avatar_split_clause,[],[f5661,f677,f731])).

fof(f5661,plain,
    ( r2_hidden(sK13(k1_tarski(sK0),k2_tarski(sK1,sK2)),k1_tarski(sK0))
    | spl22_10 ),
    inference(resolution,[],[f678,f511])).

fof(f511,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK13(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f341])).

fof(f678,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK1,sK2))
    | spl22_10 ),
    inference(avatar_component_clause,[],[f677])).

fof(f631,plain,(
    ~ spl22_1 ),
    inference(avatar_split_clause,[],[f366,f629])).

fof(f366,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f295])).

fof(f295,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f188,f294])).

fof(f294,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f188,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(ennf_transformation,[],[f182])).

fof(f182,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(negated_conjecture,[],[f181])).

fof(f181,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
%------------------------------------------------------------------------------
